import os
import asyncio
import threading
import json
import math
import re
import shutil
import subprocess
import tempfile
import time
import uuid
import urllib.parse
import urllib.request

from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from telegram import Update
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    ContextTypes,
    filters,
)

from telethon import TelegramClient, events, utils
from telethon.errors import MessageNotModifiedError, FloodWaitError
from telethon.sessions import StringSession


# ============================================================
# ENVIRONMENT VARIABLES
# ============================================================

BOT_TOKEN = os.getenv("BOT_TOKEN")
API_ID = int(os.getenv("API_ID", "0"))
API_HASH = os.getenv("API_HASH")
TELEGRAM_SESSION = os.getenv("TELEGRAM_SESSION")

PORT = int(os.getenv("PORT", "10000"))

# Instagram / Meta
INSTAGRAM_ACCESS_TOKEN = os.getenv("INSTAGRAM_ACCESS_TOKEN")
INSTAGRAM_USER_ID = os.getenv("INSTAGRAM_USER_ID")
INSTAGRAM_API_VERSION = os.getenv("INSTAGRAM_API_VERSION", "v25.0")
INSTAGRAM_API_BASE = f"https://graph.instagram.com/{INSTAGRAM_API_VERSION}"

# Minimum time between successful Instagram Reel publications.
# Default: 30 minutes (1800 seconds).
INSTAGRAM_POST_INTERVAL_SECONDS = int(
    os.getenv("INSTAGRAM_POST_INTERVAL_SECONDS", "1800")
)

# Instagram publishing window in India Standard Time (IST).
# Posts are allowed from 06:00 through 21:00 IST, inclusive.
INSTAGRAM_TIMEZONE = ZoneInfo("Asia/Kolkata")
INSTAGRAM_PUBLISH_START_HOUR = 6
INSTAGRAM_PUBLISH_END_HOUR = 21

# Send a reminder in the private Telegram storage channel when the bot is idle.
# Fixed requirement: exactly one reminder interval of at least one hour.
# The Render environment variable cannot reduce this below one hour.
UPLOAD_REMINDER_INTERVAL_SECONDS = 3600

# Public URL used by Instagram to fetch temporary Reel videos.
# Set this in Render to your public Render URL, for example:
# https://telegram-cartoon-bot-if57.onrender.com
PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "").rstrip("/")

STORAGE_CHANNEL_NAME = "Cartoon Vibes Telugu Storage"

# Telegram transfer tuning. Telethon allows up to 512 KB per file chunk.
# Larger chunks reduce request overhead for large video transfers.
TELEGRAM_TRANSFER_PART_SIZE_KB = 512


# ============================================================
# TELEGRAM STORAGE MARKERS
# ============================================================

QUEUE_MARKER = "[QUEUE_MANIFEST]"
CONFIG_MARKER = "[BOT_CONFIG]"
TITLE_REQUEST_MARKER = "[TITLE_REQUEST]"
PROCESSING_MARKER = "[PROCESSING]"

CLIP_MARKER = "[CLIP]"
UPLOAD_REMINDER_MARKER = "[UPLOAD_REMINDER]"


# ============================================================
# GLOBALS
# ============================================================

telethon_client = None
bot_application = None

admin_chat_id = None
pending_video_message_id = None

# Temporary public media registry.
# token -> {"path": local_file_path, "content_type": "video/mp4"}
public_media_files = {}
public_media_lock = threading.Lock()

# Prevent the background worker and manual /publish_queue command from
# publishing the same clip concurrently.
queue_publish_lock = asyncio.Lock()


# ============================================================
# HEALTH SERVER
# ============================================================

class HealthHandler(BaseHTTPRequestHandler):

    def _send_common_headers(self, content_type="text/plain"):
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")

    def do_HEAD(self):
        if self.path == "/health":
            self.send_response(200)
            self._send_common_headers()
            self.end_headers()
            return

        token = self.path.split("?", 1)[0].removeprefix("/media/")
        if token and token != self.path and self._media_exists(token):
            file_path = self._get_media_path(token)
            if file_path:
                try:
                    size = os.path.getsize(file_path)
                    self.send_response(200)
                    self._send_common_headers("video/mp4")
                    self.send_header("Content-Length", str(size))
                    self.send_header("Accept-Ranges", "bytes")
                    self.end_headers()
                    return
                except OSError:
                    pass

        self.send_response(404)
        self.end_headers()

    def do_GET(self):
        request_path = self.path.split("?", 1)[0]

        if request_path == "/health":
            self.send_response(200)
            self._send_common_headers()
            self.end_headers()
            self.wfile.write(b"Bot is healthy")
            return

        if request_path.startswith("/media/"):
            token = request_path[len("/media/"):]
            self.serve_media(token)
            return

        self.send_response(404)
        self.end_headers()

    def _media_exists(self, token):
        with public_media_lock:
            entry = public_media_files.get(token)
            return bool(entry and os.path.isfile(entry["path"]))

    def _get_media_path(self, token):
        with public_media_lock:
            entry = public_media_files.get(token)
            if not entry:
                return None
            return entry["path"]

    def serve_media(self, token):
        file_path = self._get_media_path(token)

        if not file_path or not os.path.isfile(file_path):
            self.send_response(404)
            self.end_headers()
            return

        try:
            file_size = os.path.getsize(file_path)
            range_header = self.headers.get("Range")

            start_byte = 0
            end_byte = file_size - 1
            status = 200

            if range_header and range_header.startswith("bytes="):
                value = range_header[6:].split(",", 1)[0].strip()

                if "-" in value:
                    left, right = value.split("-", 1)

                    if left:
                        start_byte = int(left)
                    if right:
                        end_byte = int(right)
                    elif left:
                        # RFC 7233: open-ended range.
                        end_byte = file_size - 1

                    if not left:
                        # Suffix range: bytes=-N
                        suffix_length = int(right)
                        suffix_length = min(suffix_length, file_size)
                        start_byte = file_size - suffix_length
                        end_byte = file_size - 1

                    if (
                        start_byte < 0
                        or start_byte >= file_size
                        or end_byte < start_byte
                    ):
                        self.send_response(416)
                        self.send_header(
                            "Content-Range",
                            f"bytes */{file_size}"
                        )
                        self.end_headers()
                        return

                    end_byte = min(end_byte, file_size - 1)
                    status = 206

            content_length = end_byte - start_byte + 1

            self.send_response(status)
            self._send_common_headers("video/mp4")
            self.send_header("Content-Length", str(content_length))
            self.send_header("Accept-Ranges", "bytes")

            if status == 206:
                self.send_header(
                    "Content-Range",
                    f"bytes {start_byte}-{end_byte}/{file_size}"
                )

            self.end_headers()

            with open(file_path, "rb") as media_file:
                media_file.seek(start_byte)
                remaining = content_length

                while remaining > 0:
                    chunk = media_file.read(
                        min(1024 * 1024, remaining)
                    )
                    if not chunk:
                        break

                    self.wfile.write(chunk)
                    remaining -= len(chunk)

        except (BrokenPipeError, ConnectionResetError):
            # Instagram/client disconnected before reading the whole file.
            pass
        except Exception as e:
            print(
                f"❌ Public media serving error: "
                f"{type(e).__name__}: {str(e)}"
            )

    def log_message(self, format, *args):
        return


def start_health_server():

    server = ThreadingHTTPServer(
        ("0.0.0.0", PORT),
        HealthHandler
    )

    print(
        f"Public HTTP server listening on port {PORT}."
    )

    server.serve_forever()


# ============================================================
# FIND STORAGE CHANNEL
# ============================================================

async def find_storage_channel():

    dialogs = await telethon_client.get_dialogs(
        limit=None
    )

    for dialog in dialogs:

        entity = dialog.entity

        title = getattr(
            entity,
            "title",
            None
        )

        if title == STORAGE_CHANNEL_NAME:

            return entity

    return None


# ============================================================
# SAFE TELEGRAM MESSAGE EDIT
# ============================================================

async def safe_telethon_edit_message(entity, message_id, new_text):
    """
    Edit a Telethon message safely.

    Telegram can return FLOOD_WAIT when the same message is edited too often.
    Respect the server-provided wait time and retry instead of aborting video
    processing or queue creation.
    """
    while True:
        try:
            await telethon_client.edit_message(
                entity,
                message_id,
                new_text
            )
            return True

        except MessageNotModifiedError:
            # Telegram already contains exactly this text. This is harmless.
            print(
                f"ℹ️ Telegram message {message_id} was already up to date; "
                "skipping unchanged edit."
            )
            return False

        except FloodWaitError as e:
            wait_seconds = max(1, int(getattr(e, "seconds", 1)))
            print(
                f"⏳ Telegram edit rate limit reached for message "
                f"{message_id}. Waiting {wait_seconds}s before retrying..."
            )
            await asyncio.sleep(wait_seconds + 1)


# ============================================================
# SAVE ADMIN CHAT ID
# ============================================================

async def save_admin_chat_id(chat_id):

    global admin_chat_id

    admin_chat_id = chat_id

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:

        raise RuntimeError(
            f'Could not find "{STORAGE_CHANNEL_NAME}".'
        )

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:

        text = message.message or ""

        if text.startswith(CONFIG_MARKER):

            try:

                config = json.loads(
                    text.split("\n", 1)[1]
                )

                old_chat_id = config.get(
                    "admin_chat_id"
                )

                if old_chat_id == chat_id:
                    return

                new_text = (
                    f"{CONFIG_MARKER}\n"
                    f"{json.dumps({'admin_chat_id': chat_id})}"
                )

                await safe_telethon_edit_message(
                    storage_channel,
                    message.id,
                    new_text
                )

                return

            except Exception:
                pass

    config_text = (
        f"{CONFIG_MARKER}\n"
        f"{json.dumps({'admin_chat_id': chat_id})}"
    )

    await telethon_client.send_message(
        storage_channel,
        config_text
    )


# ============================================================
# LOAD ADMIN CHAT ID
# ============================================================

async def load_admin_chat_id():

    global admin_chat_id

    if admin_chat_id:
        return admin_chat_id

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:
        return None

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:

        text = message.message or ""

        if not text.startswith(CONFIG_MARKER):
            continue

        try:

            config = json.loads(
                text.split("\n", 1)[1]
            )

            admin_chat_id = config.get(
                "admin_chat_id"
            )

            return admin_chat_id

        except Exception:
            continue

    return None


# ============================================================
# INSTAGRAM API
# ============================================================

def instagram_api_get(path, params=None):
    """
    Make a GET request to the current Instagram API using the
    Instagram Login access token stored in Render environment variables.
    """
    if not INSTAGRAM_ACCESS_TOKEN:
        raise RuntimeError("INSTAGRAM_ACCESS_TOKEN is missing.")

    if not INSTAGRAM_USER_ID:
        raise RuntimeError("INSTAGRAM_USER_ID is missing.")

    params = dict(params or {})
    params["access_token"] = INSTAGRAM_ACCESS_TOKEN

    url = f"{INSTAGRAM_API_BASE}/{path.lstrip('/')}"
    url += "?" + urllib.parse.urlencode(params)

    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": "Cartoon-Instagram-Bot/1.0"
        },
        method="GET",
    )

    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            body = response.read().decode("utf-8")
            return response.status, json.loads(body)

    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")

        try:
            data = json.loads(body)
        except Exception:
            data = {"raw": body}

        raise RuntimeError(
            f"Instagram API HTTP {e.code}: {json.dumps(data, ensure_ascii=False)}"
        )

    except Exception as e:
        raise RuntimeError(
            f"Instagram API request failed: {type(e).__name__}: {str(e)}"
        )


def instagram_api_post(path, params=None):
    """
    Make a form-encoded POST request to the Instagram Graph API.
    The access token is stored only in Render environment variables.
    """
    if not INSTAGRAM_ACCESS_TOKEN:
        raise RuntimeError("INSTAGRAM_ACCESS_TOKEN is missing.")

    if not INSTAGRAM_USER_ID:
        raise RuntimeError("INSTAGRAM_USER_ID is missing.")

    params = dict(params or {})
    params["access_token"] = INSTAGRAM_ACCESS_TOKEN

    url = f"{INSTAGRAM_API_BASE}/{path.lstrip('/')}"

    body = urllib.parse.urlencode(params).encode("utf-8")

    request = urllib.request.Request(
        url,
        data=body,
        headers={
            "User-Agent": "Cartoon-Instagram-Bot/1.0",
            "Content-Type": "application/x-www-form-urlencoded",
        },
        method="POST",
    )

    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            response_body = response.read().decode("utf-8")
            return response.status, json.loads(response_body)

    except urllib.error.HTTPError as e:
        body_text = e.read().decode("utf-8", errors="replace")

        try:
            data = json.loads(body_text)
        except Exception:
            data = {"raw": body_text}

        raise RuntimeError(
            f"Instagram API HTTP {e.code}: "
            f"{json.dumps(data, ensure_ascii=False)}"
        )

    except Exception as e:
        raise RuntimeError(
            f"Instagram API POST failed: "
            f"{type(e).__name__}: {str(e)}"
        )


def register_public_media(file_path):
    """
    Register one local MP4 so Instagram can fetch it over HTTPS.
    Returns (token, public_url).
    """
    if not PUBLIC_BASE_URL:
        raise RuntimeError(
            "PUBLIC_BASE_URL is missing in Render."
        )

    if not os.path.isfile(file_path):
        raise RuntimeError(
            f"Media file does not exist: {file_path}"
        )

    token = uuid.uuid4().hex

    with public_media_lock:
        public_media_files[token] = {
            "path": file_path,
            "content_type": "video/mp4",
        }

    public_url = f"{PUBLIC_BASE_URL}/media/{token}"

    print(f"🌐 Temporary public media URL created: {public_url}")

    return token, public_url


def unregister_public_media(token):
    if not token:
        return

    with public_media_lock:
        public_media_files.pop(token, None)

    print(f"🗑️ Temporary public media URL removed: {token}")


def publish_reel_from_file(file_path, title, part_index, total_parts):
    """
    Upload one local video to Instagram as a Reel using the
    URL-based Instagram publishing flow.

    Important:
    Instagram fetches the video from the temporary public URL.
    The Telegram clip is NOT deleted by this function.
    """
    token = None

    try:
        token, public_url = register_public_media(file_path)

        caption = build_instagram_caption(
            title,
            part_index,
            total_parts
        )

        print(
            f"📤 Creating Instagram Reel container "
            f"for Part {part_index}/{total_parts}..."
        )

        _, container_data = instagram_api_post(
            f"{INSTAGRAM_USER_ID}/media",
            {
                "media_type": "REELS",
                "video_url": public_url,
                "caption": caption,
                "share_to_feed": "false",
            }
        )

        creation_id = container_data.get("id")

        if not creation_id:
            raise RuntimeError(
                "Instagram did not return a creation/container ID.\n"
                f"Response: {json.dumps(container_data, ensure_ascii=False)}"
            )

        print(
            f"✅ Instagram container created: {creation_id}"
        )

        # Instagram needs time to download/transcode the video.
        # Poll until the container is ready.
        max_attempts = 60
        poll_seconds = 5

        for attempt in range(1, max_attempts + 1):

            time.sleep(poll_seconds)

            _, status_data = instagram_api_get(
                creation_id,
                {
                    "fields": "status_code,status"
                }
            )

            status_code = (
                status_data.get("status_code")
                or status_data.get("status")
                or ""
            )

            print(
                f"📡 Instagram processing status "
                f"{attempt}/{max_attempts}: {status_code}"
            )

            if status_code == "FINISHED":
                break

            if status_code in {
                "ERROR",
                "EXPIRED",
                "FAILED",
            }:
                raise RuntimeError(
                    "Instagram video processing failed.\n"
                    f"Status: {json.dumps(status_data, ensure_ascii=False)}"
                )

        else:
            raise RuntimeError(
                "Instagram video processing timed out after "
                f"{max_attempts * poll_seconds} seconds."
            )

        print(
            f"🚀 Publishing Instagram Reel: {creation_id}"
        )

        _, publish_data = instagram_api_post(
            f"{INSTAGRAM_USER_ID}/media_publish",
            {
                "creation_id": creation_id
            }
        )

        media_id = publish_data.get("id")

        if not media_id:
            raise RuntimeError(
                "Instagram did not return a published media ID.\n"
                f"Response: {json.dumps(publish_data, ensure_ascii=False)}"
            )

        print(
            f"🎉 Instagram Reel published successfully: {media_id}"
        )

        return media_id

    finally:
        # The file itself is deleted by the caller's temp-directory
        # cleanup. The public route disappears immediately.
        unregister_public_media(token)


async def test_instagram(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    """
    Verify the Instagram access token and Instagram User ID.
    The token itself is never sent to Telegram.
    """
    try:
        if not INSTAGRAM_ACCESS_TOKEN:
            await update.message.reply_text(
                "❌ INSTAGRAM_ACCESS_TOKEN is missing in Render."
            )
            return

        if not INSTAGRAM_USER_ID:
            await update.message.reply_text(
                "❌ INSTAGRAM_USER_ID is missing in Render."
            )
            return

        await update.message.reply_text(
            "🔎 Checking Instagram API connection..."
        )

        status_code, data = instagram_api_get(
            INSTAGRAM_USER_ID,
            {
                "fields": "id,username"
            }
        )

        instagram_id = data.get("id")
        username = data.get("username")

        await update.message.reply_text(
            "✅ INSTAGRAM API CONNECTION WORKS!\n\n"
            f"Username: @{username}\n"
            f"Instagram User ID: {instagram_id}\n"
            f"API version: {INSTAGRAM_API_VERSION}\n"
            f"HTTP status: {status_code}\n\n"
            "🔐 Access token was NOT displayed."
        )

    except Exception as e:
        await update.message.reply_text(
            "❌ INSTAGRAM API TEST FAILED\n\n"
            f"Error: {type(e).__name__}\n"
            f"{str(e)}"
        )


# ============================================================
# START
# ============================================================

async def start(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    try:

        chat_id = update.effective_chat.id

        await save_admin_chat_id(
            chat_id
        )

        await update.message.reply_text(
            "👋 Hello!\n\n"
            "✅ Your Telegram account is connected.\n\n"
            "🎬 Upload the ORIGINAL video "
            f"directly to {STORAGE_CHANNEL_NAME}.\n\n"
            "I'll detect it automatically and "
            "ask for the title."
        )

    except Exception as e:

        await update.message.reply_text(
            "❌ Could not save configuration.\n\n"
            f"{type(e).__name__}: {str(e)}"
        )


# ============================================================
# TELEGRAM CONNECTION TEST
# ============================================================

async def test_telegram(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    try:

        me = await telethon_client.get_me()

        name = " ".join(
            part
            for part in [
                me.first_name,
                me.last_name
            ]
            if part
        )

        await update.message.reply_text(
            f"✅ Telethon connected!\n\n"
            f"Account: {name}\n"
            f"User ID: {me.id}"
        )

    except Exception as e:

        await update.message.reply_text(
            "❌ Telethon connection failed:\n"
            f"{type(e).__name__}: {str(e)}"
        )


# ============================================================
# TITLE REQUEST
# ============================================================

async def save_title_request(
    video_message_id
):

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:

        raise RuntimeError(
            f'Could not find "{STORAGE_CHANNEL_NAME}".'
        )

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    request_text = (
        f"{TITLE_REQUEST_MARKER}\n"
        f"{json.dumps({'video_message_id': video_message_id})}"
    )

    for message in messages:

        text = message.message or ""

        if text.startswith(
            TITLE_REQUEST_MARKER
        ):

            await safe_telethon_edit_message(
                storage_channel,
                message.id,
                request_text
            )

            return

    await telethon_client.send_message(
        storage_channel,
        request_text
    )


async def load_title_request():

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:
        return None

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:

        text = message.message or ""

        if not text.startswith(
            TITLE_REQUEST_MARKER
        ):
            continue

        try:

            data = json.loads(
                text.split("\n", 1)[1]
            )

            return data.get(
                "video_message_id"
            )

        except Exception:
            continue

    return None


async def delete_title_request():

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:
        return

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:

        text = message.message or ""

        if text.startswith(
            TITLE_REQUEST_MARKER
        ):

            await telethon_client.delete_messages(
                storage_channel,
                message.id
            )

            return


# ============================================================
# PROCESSING STATE
# ============================================================

async def save_processing_state(
    video_message_id,
    title
):

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:
        return

    state = {
        "video_message_id": video_message_id,
        "title": title,
        "started_at": datetime.now(
            timezone.utc
        ).isoformat()
    }

    text = (
        f"{PROCESSING_MARKER}\n"
        f"{json.dumps(state, indent=2)}"
    )

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:

        existing = message.message or ""

        if existing.startswith(
            PROCESSING_MARKER
        ):

            await safe_telethon_edit_message(
                storage_channel,
                message.id,
                text
            )

            return

    await telethon_client.send_message(
        storage_channel,
        text
    )


async def load_processing_state():
    """Return the active persistent processing record, if one exists."""

    storage_channel = await find_storage_channel()
    if storage_channel is None:
        return None

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:
        text = message.message or ""
        if not text.startswith(PROCESSING_MARKER):
            continue
        try:
            return json.loads(text.split("\n", 1)[1])
        except Exception:
            continue

    return None


async def delete_processing_state():

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:
        return

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:

        text = message.message or ""

        if text.startswith(
            PROCESSING_MARKER
        ):

            await telethon_client.delete_messages(
                storage_channel,
                message.id
            )

            return


# ============================================================
# SAFE FILENAME
# ============================================================

def safe_filename(text):

    text = text.strip()

    text = re.sub(
        r'[<>:"/\\|?*\x00-\x1F]',
        "",
        text
    )

    text = re.sub(
        r"\s+",
        " ",
        text
    )

    if not text:
        text = "Video"

    return text[:150]


# ============================================================
# INSTAGRAM HASHTAGS / CAPTION
# ============================================================

KNOWN_TITLE_TAGS = {
    "doraemon": "#doraemon",
    "shinchan": "#shinchan",
    "crayon shinchan": "#crayonshinchan",
    "naruto": "#naruto",
    "one piece": "#onepiece",
    "onepiece": "#onepiece",
    "solo leveling": "#sololeveling",
    "sololeveling": "#sololeveling",
    "chainsaw man": "#chainsawman",
    "chainsawman": "#chainsawman",
    "jujutsu kaisen": "#jujutsukaisen",
    "demon slayer": "#demonslayer",
    "dragon ball": "#dragonball",
    "dragonball": "#dragonball",
    "attack on titan": "#attackontitan",
    "pokemon": "#pokemon",
    "pokemon": "#pokemon",
}

ANIME_KEYWORDS = {
    "anime", "naruto", "one piece", "onepiece", "solo leveling",
    "sololeveling", "chainsaw man", "chainsawman", "jujutsu",
    "demon slayer", "dragon ball", "dragonball", "attack on titan",
    "pokemon", "bleach", "black clover", "my hero academia",
}


def build_instagram_hashtags(title):
    """
    Build a small set of relevant hashtags from the title.
    This does NOT claim that hashtags guarantee trending; it keeps tags
    related to the actual cartoon/anime title instead of unrelated spam.
    """
    lowered = title.lower()

    tags = []

    if any(keyword in lowered for keyword in ANIME_KEYWORDS):
        tags.extend(["#anime", "#animeclips", "#animefans"])
    else:
        tags.extend(["#cartoon", "#cartoonclips", "#animation"])

    for phrase, tag in KNOWN_TITLE_TAGS.items():
        if phrase in lowered and tag not in tags:
            tags.append(tag)

    # Add a clean hashtag from the title itself when possible.
    words = re.findall(r"[A-Za-z0-9]+", title)
    ignored = {
        "episode", "ep", "part", "clip", "video", "season",
        "the", "and", "of", "a", "an"
    }
    meaningful = [w.lower() for w in words if w.lower() not in ignored and not w.isdigit()]

    if meaningful:
        title_tag = "#" + "".join(meaningful)
        if len(title_tag) <= 60 and title_tag not in tags:
            tags.append(title_tag)

    # Broad discovery tag, while keeping the total small and relevant.
    tags.append("#reels")

    # Remove duplicates while preserving order.
    unique_tags = []
    for tag in tags:
        if tag not in unique_tags:
            unique_tags.append(tag)

    return " ".join(unique_tags[:8])


def build_instagram_caption(title, part_index, total_parts):
    hashtags = build_instagram_hashtags(title)
    return (
        f"{title}\n\n"
        f"Part {part_index}/{total_parts}\n\n"
        f"{hashtags}"
    )


# ============================================================
# SPLIT VIDEO
# ============================================================

async def get_video_duration(input_path):
    """Return the source video's duration in seconds using ffprobe."""
    command = [
        "ffprobe",
        "-v", "error",
        "-show_entries", "format=duration",
        "-of", "default=noprint_wrappers=1:nokey=1",
        input_path,
    ]

    process = await asyncio.create_subprocess_exec(
        *command,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )

    stdout, stderr = await process.communicate()

    if process.returncode != 0:
        raise RuntimeError(
            "Could not read video duration with ffprobe.\n"
            f"{stderr.decode(errors='replace').strip()}"
        )

    try:
        duration = float(stdout.decode().strip())
    except ValueError as e:
        raise RuntimeError("ffprobe returned an invalid video duration.") from e

    if duration <= 0:
        raise RuntimeError("Video duration is zero or invalid.")

    return duration


def format_duration(seconds):
    seconds = max(0, int(seconds))
    hours, remainder = divmod(seconds, 3600)
    minutes, seconds = divmod(remainder, 60)
    if hours:
        return f"{hours}h {minutes:02d}m {seconds:02d}s"
    return f"{minutes}m {seconds:02d}s"


def progress_bar(percent, width=20):
    percent = max(0.0, min(100.0, float(percent)))
    filled = int(round(width * percent / 100))
    return "█" * filled + "░" * (width - filled)


class TelegramProgressReporter:
    """Rate-limit progress edits and never queue a backlog of Telegram edits."""

    def __init__(self, bot, chat_id, message_id, min_interval=10.0):
        self.bot = bot
        self.chat_id = chat_id
        self.message_id = message_id
        self.min_interval = min_interval
        self.last_update = 0.0
        self.last_text = None
        self.lock = asyncio.Lock()
        self.pending_text = None
        self.pending_force = False
        self.pending_task = None

    async def edit(self, text, force=False):
        if text == self.last_text:
            return False

        async with self.lock:
            now = time.monotonic()
            if not force and now - self.last_update < self.min_interval:
                return False
            if text == self.last_text:
                return False

            try:
                await self.bot.edit_message_text(
                    chat_id=self.chat_id,
                    message_id=self.message_id,
                    text=text,
                )
                self.last_update = time.monotonic()
                self.last_text = text
                return True
            except Exception as e:
                # Progress UI must never abort the actual video operation.
                print(
                    f"⚠️ Progress message update failed: "
                    f"{type(e).__name__}: {str(e)}"
                )
                return False

    async def _flush_pending(self):
        try:
            while self.pending_text is not None:
                now = time.monotonic()
                wait = self.min_interval - (now - self.last_update)
                if wait > 0:
                    await asyncio.sleep(wait)

                text = self.pending_text
                force = self.pending_force
                self.pending_text = None
                self.pending_force = False

                await self.edit(text, force=force)
        finally:
            self.pending_task = None

    def schedule(self, text, force=False):
        """Keep only the newest pending progress update."""
        self.pending_text = text
        self.pending_force = self.pending_force or force

        if self.pending_task is None or self.pending_task.done():
            self.pending_task = asyncio.create_task(
                self._flush_pending()
            )


async def split_video(
    input_path,
    output_directory,
    progress_reporter=None,
    title="Video",
):
    """Fast keyframe-aware stream-copy splitter targeting ~60-second clips."""
    os.makedirs(output_directory, exist_ok=True)

    # Get keyframe timestamps. No video is decoded/re-encoded.
    command = [
        "ffprobe", "-v", "error",
        "-skip_frame", "nokey",
        "-select_streams", "v:0",
        "-show_entries", "frame=best_effort_timestamp_time",
        "-of", "csv=p=0",
        input_path,
    ]
    process = await asyncio.create_subprocess_exec(
        *command, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
    )
    stdout, stderr = await process.communicate()
    if process.returncode != 0:
        raise RuntimeError(f"Could not read video keyframes.\n{stderr.decode(errors='replace').strip()}")

    keyframes = []
    for line in stdout.decode(errors="replace").splitlines():
        try:
            value = float(line.strip())
            if value >= 0:
                keyframes.append(value)
        except ValueError:
            continue

    duration = await get_video_duration(input_path)
    if not keyframes:
        raise RuntimeError("No video keyframes were found.")

    # Pick boundaries between 55 and 65 seconds, preferring 60 seconds.
    boundaries = []
    current = 0.0
    while duration - current > 60.0:
        candidates = [k for k in keyframes if current + 55.0 <= k <= current + 65.0]
        if not candidates:
            raise RuntimeError(
                f"No safe keyframe found between {current + 55:.1f}s and {current + 65:.1f}s. "
                "Cannot create a safe <=65 second stream-copy clip."
            )
        boundary = min(candidates, key=lambda k: abs(k - (current + 60.0)))
        boundaries.append(boundary)
        current = boundary

    output_pattern = os.path.join(output_directory, "part_%03d.mp4")
    command = [
        "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
        "-i", input_path,
        "-map", "0:v:0", "-map", "0:a:0?",
        "-c", "copy",
        "-f", "segment",
        "-segment_times", ",".join(f"{x:.3f}" for x in boundaries),
        "-reset_timestamps", "1",
        "-segment_format", "mp4",
        output_pattern,
    ]
    print("Running FAST stream-copy FFmpeg:")
    print(" ".join(command))

    process = await asyncio.create_subprocess_exec(
        *command, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
    )
    stdout, stderr = await process.communicate()
    if process.returncode != 0:
        error_text = stderr.decode(errors="replace").strip()
        raise RuntimeError(f"FFmpeg failed to split the video.\n{error_text[-2000:]}")

    clips = sorted(
        os.path.join(output_directory, name)
        for name in os.listdir(output_directory)
        if name.startswith("part_") and name.endswith(".mp4")
    )
    if not clips:
        raise RuntimeError("FFmpeg completed but produced no clips.")

    if progress_reporter:
        await progress_reporter.edit(
            "✂️ FAST SPLITTING COMPLETE\n\n"
            f"🎬 {title}\n\n"
            f"📹 Duration: {format_duration(duration)}\n"
            f"✂️ Parts created: {len(clips)}\n"
            "⚡ Stream copy: no re-encoding",
            force=True,
        )
    return clips, duration


# ============================================================
# FAST TELEGRAM DOWNLOAD
# ============================================================

async def fast_download_telegram_media(message, output_path, progress_callback=None):
    """Download Telegram media using the maximum 512 KB request size."""
    dc_id, location = utils.get_input_location(message)
    file_size = getattr(getattr(message, "file", None), "size", None)

    downloaded = await telethon_client.download_file(
        location,
        file=output_path,
        part_size_kb=TELEGRAM_TRANSFER_PART_SIZE_KB,
        file_size=file_size,
        progress_callback=progress_callback,
        dc_id=dc_id,
    )

    return downloaded


async def download_original_when_ready(message_id, output_path, progress_callback=None):
    """
    Download an original video only after Telegram has made the media
    completely available. A NewMessage event can arrive while a large
    client upload is still being finalized, so retry the exact same fast
    download instead of failing the whole job at the end of a partial
    transfer.

    This does not change the transfer chunk size or the splitter.
    """
    last_error = None

    for attempt in range(1, 13):
        current_message = await telethon_client.get_messages(
            await find_storage_channel(),
            ids=message_id,
        )

        if not current_message or not current_message.video:
            last_error = RuntimeError(
                "Original video is not currently available on Telegram."
            )
        else:
            expected_size = getattr(getattr(current_message, "file", None), "size", None)

            try:
                # If a previous attempt already wrote the complete file, keep it.
                # Telethon can raise at the very end of a transfer even though
                # all expected bytes are already on disk.
                if os.path.exists(output_path):
                    existing_size = os.path.getsize(output_path)
                    if expected_size is None or existing_size >= expected_size:
                        print(
                            f"✅ Original video is already complete: "
                            f"{existing_size} bytes."
                        )
                        return output_path

                    # Only remove a genuinely incomplete previous attempt.
                    os.remove(output_path)

                downloaded = await fast_download_telegram_media(
                    current_message,
                    output_path,
                    progress_callback=progress_callback,
                )

                if os.path.exists(output_path):
                    actual_size = os.path.getsize(output_path)

                    # Treat the local file as successful when it contains the
                    # complete Telegram media, even if Telethon returned a
                    # falsy value or raised immediately after the final write.
                    if expected_size is None or actual_size >= expected_size:
                        print(
                            f"✅ Original video download complete: "
                            f"{actual_size} bytes."
                        )
                        return output_path

                    last_error = RuntimeError(
                        f"Telegram returned an incomplete video "
                        f"({actual_size} / {expected_size} bytes)."
                    )
                else:
                    last_error = RuntimeError(
                        "Telegram download returned no completed file."
                    )

            except Exception as exc:
                # IMPORTANT: Do not throw away a complete file merely because
                # Telethon raised after the final bytes were written.
                if os.path.exists(output_path):
                    actual_size = os.path.getsize(output_path)
                    if expected_size is None or actual_size >= expected_size:
                        print(
                            f"✅ Download reached the expected size despite "
                            f"a final Telethon exception: {actual_size} bytes."
                        )
                        return output_path

                last_error = exc

        if attempt < 12:
            print(
                f"⏳ Original video is not ready yet (attempt {attempt}/12). "
                "Waiting 5 seconds before retrying..."
            )
            await asyncio.sleep(5)

    if last_error:
        raise RuntimeError(
            f"Failed to download original video after waiting for Telegram upload completion: {last_error}"
        )

    raise RuntimeError(
        "Failed to download original video after waiting for Telegram upload completion."
    )


# ============================================================
# CREATE QUEUE MANIFEST
# ============================================================

async def create_automatic_queue(
    storage_channel,
    title,
    original_message_id,
    uploaded_clips
):
    """
    Create a compact persistent queue.

    IMPORTANT: Telegram messages have a hard text-length limit. The previous
    queue stored a large object for every clip and eventually exceeded that
    limit. Queue V2 stores only Telegram message IDs plus aggregate state.
    """

    now = datetime.now(timezone.utc).isoformat()
    queue_id = f"queue_{now}"

    queue = {
        "queue_version": 2,
        "queue_id": queue_id,
        "title": title,
        "created_at": now,
        "status": "PENDING",
        "processing_complete": False,
        "original_telegram_message_id": original_message_id,
        "total_clips": len(uploaded_clips),
        "next_clip_index": 1,
        "clip_message_ids": [message.id for message in uploaded_clips],
        "last_published_at": None,
        "retry_after": None,
    }

    manifest_json = json.dumps(
        queue,
        ensure_ascii=False,
        separators=(",", ":")
    )

    manifest_text = (
        f"{QUEUE_MARKER}\n\n"
        f"Cartoon Instagram Bot Queue\n\n"
        f"{manifest_json}"
    )

    manifest_message = await telethon_client.send_message(
        storage_channel,
        manifest_text
    )

    return queue, manifest_message


async def append_clip_to_queue(
    manifest_message,
    queue,
    message,
    title,
    index
):
    """Persist one clip using only its Telegram message ID."""

    clip_message_ids = queue.setdefault(
        "clip_message_ids",
        []
    )

    if message.id not in clip_message_ids:
        clip_message_ids.append(message.id)

    queue["total_clips"] = len(clip_message_ids)

    await save_queue_manifest(
        manifest_message,
        queue
    )


async def find_queue_manifests():
    """Load all persistent queue manifests from Telegram, oldest first."""
    storage_channel = await find_storage_channel()

    if storage_channel is None:
        return []

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=200
    )

    manifests = []

    for message in messages:
        text = message.message or ""

        if not text.startswith(QUEUE_MARKER):
            continue

        try:
            json_text = text.split("\n\n", 2)[-1]
            queue = json.loads(json_text)

            manifests.append({
                "message": message,
                "queue": queue,
            })

        except Exception as e:
            print(
                f"⚠️ Could not parse queue manifest "
                f"{message.id}: {type(e).__name__}: {str(e)}"
            )

    # Oldest queue first so a newer upload cannot jump ahead of an older one.
    manifests.sort(
        key=lambda item: item["queue"].get("created_at", "")
    )

    return manifests


async def save_queue_manifest(manifest_message, queue):
    """Persist the compact queue state safely in its Telegram manifest message."""
    manifest_json = json.dumps(
        queue,
        ensure_ascii=False,
        separators=(",", ":")
    )

    manifest_text = (
        f"{QUEUE_MARKER}\n\n"
        f"Cartoon Instagram Bot Queue\n\n"
        f"{manifest_json}"
    )

    # Stay safely below Telegram's 4096-character message limit.
    if len(manifest_text) > 3500:
        raise RuntimeError(
            "Queue manifest is unexpectedly large. "
            "The compact queue format was not preserved."
        )

    storage_channel = await find_storage_channel()

    if storage_channel is None:
        raise RuntimeError(
            f'Could not find "{STORAGE_CHANNEL_NAME}".'
        )

    # safe_telethon_edit_message handles MessageNotModifiedError and
    # Telegram FLOOD_WAIT responses without aborting video processing.
    await safe_telethon_edit_message(
        storage_channel,
        manifest_message.id,
        manifest_text
    )


# ============================================================
# INSTAGRAM QUEUE PUBLISHER
# ============================================================


async def publish_one_queue_clip(
    manifest_message,
    queue,
    clip
):
    storage_channel = await find_storage_channel()

    if storage_channel is None:
        raise RuntimeError(
            f'Could not find "{STORAGE_CHANNEL_NAME}".'
        )

    clip_index = clip.get("index")
    telegram_message_id = clip.get("telegram_message_id")
    title = queue.get("title", "Cartoon")

    if not telegram_message_id:
        raise RuntimeError(
            f"Clip {clip_index} has no Telegram message ID."
        )

    print(
        f"📦 Loading Telegram clip {clip_index} "
        f"(message {telegram_message_id})..."
    )

    message = await telethon_client.get_messages(
        storage_channel,
        ids=telegram_message_id
    )

    if not message:
        raise RuntimeError(
            f"Telegram clip message {telegram_message_id} "
            f"could not be found."
        )

    if not message.video:
        raise RuntimeError(
            f"Telegram message {telegram_message_id} "
            f"is not a video."
        )

    temp_directory = tempfile.mkdtemp(
        prefix="instagram_publish_"
    )

    try:
        safe_name = safe_filename(
            clip.get("filename")
            or f"{title} Part {clip_index}.mp4"
        )

        if not safe_name.lower().endswith(".mp4"):
            safe_name += ".mp4"

        local_path = os.path.join(
            temp_directory,
            safe_name
        )

        print(
            f"📥 Downloading Telegram clip "
            f"{clip_index}/{queue.get('total_clips')}..."
        )

        expected_size = getattr(getattr(message, "file", None), "size", None)
        last_download_error = None

        # The low-level Telethon download can return a falsy value even when
        # the requested file was written successfully. It can also raise
        # immediately after the final bytes are written. Never treat that
        # situation as a failed download when the local file is complete.
        for attempt in range(1, 4):
            try:
                downloaded = await fast_download_telegram_media(
                    message,
                    local_path,
                )

                if os.path.isfile(local_path):
                    actual_size = os.path.getsize(local_path)

                    if expected_size is None or actual_size >= expected_size:
                        print(
                            f"✅ Telegram clip {clip_index} download complete: "
                            f"{actual_size} bytes."
                        )
                        break

                    last_download_error = RuntimeError(
                        f"Telegram clip {clip_index} download is incomplete "
                        f"({actual_size} / {expected_size} bytes)."
                    )
                else:
                    last_download_error = RuntimeError(
                        f"Telegram clip {clip_index} download produced no local file."
                    )

            except Exception as download_error:
                last_download_error = download_error

                # Telethon may raise after writing the final bytes. Check the
                # file before deciding that the download really failed.
                if os.path.isfile(local_path):
                    actual_size = os.path.getsize(local_path)

                    if expected_size is None or actual_size >= expected_size:
                        print(
                            f"✅ Telegram clip {clip_index} reached the expected "
                            f"size despite a final Telethon exception: "
                            f"{actual_size} bytes."
                        )
                        break

            if attempt < 3:
                print(
                    f"⏳ Telegram clip {clip_index} download incomplete "
                    f"(attempt {attempt}/3). Retrying..."
                )
                if os.path.exists(local_path):
                    os.remove(local_path)
                await asyncio.sleep(2)
        else:
            raise RuntimeError(
                f"Failed to download Telegram clip {clip_index}: "
                f"{type(last_download_error).__name__}: {last_download_error}"
            )

        media_id = await asyncio.to_thread(
            publish_reel_from_file,
            local_path,
            title,
            clip_index,
            queue.get("total_clips", 1)
        )

        # Instagram has confirmed publication. Mark it as published
        # BEFORE attempting Telegram cleanup, so a Telegram deletion
        # problem can never cause a duplicate Instagram post.
        clip["status"] = "PUBLISHED"
        clip["instagram_status"] = "PUBLISHED"
        clip["instagram_media_id"] = media_id
        clip["posted_at"] = datetime.now(
            timezone.utc
        ).isoformat()

        try:
            # ONLY now delete the Telegram clip.
            await telethon_client.delete_messages(
                storage_channel,
                telegram_message_id
            )
            clip["deleted_from_telegram"] = True

        except Exception as delete_error:
            # Publication succeeded, so do not retry Instagram.
            clip["deleted_from_telegram"] = False

            print(
                "⚠️ Instagram publication succeeded but Telegram "
                "clip deletion failed:\n"
                f"{type(delete_error).__name__}: {str(delete_error)}"
            )

        return media_id

    except Exception:
        # Keep the Telegram clip for retry when Instagram publication
        # itself fails.
        clip["status"] = "FAILED"
        clip["instagram_status"] = "FAILED"
        raise

    finally:
        shutil.rmtree(
            temp_directory,
            ignore_errors=True
        )


async def get_last_successful_instagram_publish_time(manifests):
    """Return the latest successful Instagram publication timestamp."""

    latest = None

    for item in manifests:
        queue = item.get("queue", {})

        value = queue.get("last_published_at")
        if value:
            try:
                timestamp = datetime.fromisoformat(
                    value.replace("Z", "+00:00")
                )
                if timestamp.tzinfo is None:
                    timestamp = timestamp.replace(tzinfo=timezone.utc)
                if latest is None or timestamp > latest:
                    latest = timestamp
            except Exception:
                pass

        # Backward compatibility with old queue manifests.
        for clip in queue.get("clips", []):
            if clip.get("instagram_status") != "PUBLISHED":
                continue
            posted_at = clip.get("posted_at")
            if not posted_at:
                continue
            try:
                timestamp = datetime.fromisoformat(
                    posted_at.replace("Z", "+00:00")
                )
                if timestamp.tzinfo is None:
                    timestamp = timestamp.replace(tzinfo=timezone.utc)
                if latest is None or timestamp > latest:
                    latest = timestamp
            except Exception:
                pass

    return latest


async def _process_pending_queues():
    """Publish at most one Reel when a queue is ready and its cooldown allows it."""

    if not INSTAGRAM_ACCESS_TOKEN or not INSTAGRAM_USER_ID:
        print("⚠️ Instagram credentials are missing. Queue publisher is disabled.")
        return

    if not PUBLIC_BASE_URL:
        print("⚠️ PUBLIC_BASE_URL is missing. Queue publisher is disabled.")
        return

    manifests = await find_queue_manifests()

    last_publish = await get_last_successful_instagram_publish_time(manifests)
    if last_publish is not None:
        elapsed = (
            datetime.now(timezone.utc) - last_publish
        ).total_seconds()
        if elapsed < INSTAGRAM_POST_INTERVAL_SECONDS:
            remaining = int(INSTAGRAM_POST_INTERVAL_SECONDS - elapsed)
            print(
                "⏳ Instagram posting cooldown active. "
                f"Next Reel allowed in {remaining // 60}m {remaining % 60}s."
            )
            return

    for item in manifests:
        manifest_message = item["message"]
        queue = item["queue"]

        if queue.get("status") == "COMPLETED":
            continue

        # HARD BARRIER: Instagram can never publish until the splitter and
        # every Telegram clip upload have completed.
        if not queue.get("processing_complete", False):
            print(
                f"⏳ Queue {queue.get('queue_id')} is not complete yet. "
                "Instagram publishing is blocked."
            )
            continue

        # V2 compact queue.
        if queue.get("queue_version") == 2 and "clip_message_ids" in queue:
            total = int(queue.get("total_clips", 0))
            next_index = int(queue.get("next_clip_index", 1))

            retry_after = queue.get("retry_after")
            if retry_after:
                try:
                    retry_time = datetime.fromisoformat(
                        retry_after.replace("Z", "+00:00")
                    )
                    if retry_time.tzinfo is None:
                        retry_time = retry_time.replace(tzinfo=timezone.utc)
                    if datetime.now(timezone.utc) < retry_time:
                        print(
                            f"⏳ Queue {queue.get('queue_id')} is waiting "
                            f"until {retry_time.isoformat()} after a previous failure."
                        )
                        continue
                    queue["retry_after"] = None
                    await save_queue_manifest(manifest_message, queue)
                except Exception:
                    queue["retry_after"] = None

            if next_index > total:
                queue["status"] = "COMPLETED"
                await save_queue_manifest(manifest_message, queue)
                if admin_chat_id:
                    await bot_application.bot.send_message(
                        chat_id=admin_chat_id,
                        text=(
                            "🎉 INSTAGRAM QUEUE COMPLETE!\n\n"
                            f"🎬 {queue.get('title', 'Cartoon')}\n"
                            f"📤 Published: {total}\n"
                            "🗑️ Successfully published clips were removed from Telegram."
                        )
                    )
                continue

            clip_message_ids = queue.get("clip_message_ids", [])
            if next_index > len(clip_message_ids):
                raise RuntimeError(
                    f"Queue {queue.get('queue_id')} is missing the Telegram "
                    f"message ID for Part {next_index}."
                )

            title = queue.get("title", "Cartoon")
            telegram_message_id = clip_message_ids[next_index - 1]

            clip = {
                "index": next_index,
                "telegram_message_id": telegram_message_id,
                "filename": f"{safe_filename(title)} Part {next_index}.mp4",
                "status": "PUBLISHING",
                "instagram_status": "PUBLISHING",
                "instagram_media_id": None,
                "posted_at": None,
                "deleted_from_telegram": False,
            }

            try:
                media_id = await publish_one_queue_clip(
                    manifest_message,
                    queue,
                    clip
                )

                # Advance only after Instagram has confirmed publication.
                queue["next_clip_index"] = next_index + 1
                queue["last_published_at"] = datetime.now(timezone.utc).isoformat()
                queue["retry_after"] = None

                if queue["next_clip_index"] > total:
                    queue["status"] = "COMPLETED"

                await save_queue_manifest(manifest_message, queue)

                if admin_chat_id:
                    await bot_application.bot.send_message(
                        chat_id=admin_chat_id,
                        text=(
                            "✅ INSTAGRAM REEL PUBLISHED!\n\n"
                            f"🎬 {title}\n"
                            f"📌 Part: {next_index}/{total}\n"
                            f"🆔 Instagram Media ID: {media_id}\n\n"
                            + (
                                "🗑️ Telegram clip deleted after successful publishing."
                                if clip.get("deleted_from_telegram")
                                else "⚠️ Instagram published successfully, but Telegram cleanup failed."
                            )
                        )
                    )
                return

            except Exception as e:
                error_text = str(e)

                # Meta's Media Publish Limit Exceeded should not be hammered
                # every minute. It is a rolling publishing-quota condition.
                if (
                    "2207042" in error_text
                    or "Media Publish Limit Exceeded" in error_text
                ):
                    retry_seconds = 24 * 60 * 60
                else:
                    retry_seconds = 10 * 60

                queue["retry_after"] = (
                    datetime.now(timezone.utc)
                    + timedelta(seconds=retry_seconds)
                ).isoformat()

                try:
                    await save_queue_manifest(manifest_message, queue)
                except Exception as manifest_error:
                    print(
                        "⚠️ Could not save Instagram retry state: "
                        f"{type(manifest_error).__name__}: {str(manifest_error)}"
                    )

                print(
                    "❌ Instagram publishing failed. "
                    f"{type(e).__name__}: {error_text}. "
                    f"Retry backoff: {retry_seconds}s."
                )

                if admin_chat_id:
                    await bot_application.bot.send_message(
                        chat_id=admin_chat_id,
                        text=(
                            "❌ INSTAGRAM REEL PUBLISH FAILED\n\n"
                            f"🎬 {title}\n"
                            f"📌 Part: {next_index}/{total}\n"
                            f"Error: {type(e).__name__}\n"
                            f"{error_text}\n\n"
                            "⚠️ The Telegram clip was NOT deleted.\n"
                            f"⏳ Automatic retry is delayed for "
                            f"{retry_seconds // 3600 if retry_seconds >= 3600 else retry_seconds // 60}"
                            f"{' hours' if retry_seconds >= 3600 else ' minutes'}."
                        )
                    )
                return

        # Legacy queue compatibility.
        clips = queue.get("clips", [])
        target_clip = next(
            (
                clip for clip in clips
                if clip.get("instagram_status") != "PUBLISHED"
            ),
            None
        )

        if target_clip is None:
            queue["status"] = "COMPLETED"
            queue["next_clip_index"] = queue.get("total_clips", len(clips)) + 1
            await save_queue_manifest(manifest_message, queue)
            continue

        clip_index = target_clip.get("index")
        try:
            media_id = await publish_one_queue_clip(
                manifest_message,
                queue,
                target_clip
            )
            queue["next_clip_index"] = int(clip_index) + 1
            if queue["next_clip_index"] > queue.get("total_clips", len(clips)):
                queue["status"] = "COMPLETED"
            await save_queue_manifest(manifest_message, queue)
            if admin_chat_id:
                await bot_application.bot.send_message(
                    chat_id=admin_chat_id,
                    text=(
                        "✅ INSTAGRAM REEL PUBLISHED!\n\n"
                        f"🎬 {queue.get('title', 'Cartoon')}\n"
                        f"📌 Part: {clip_index}/{queue.get('total_clips', len(clips))}\n"
                        f"🆔 Instagram Media ID: {media_id}\n\n"
                        + (
                            "🗑️ Telegram clip deleted after successful publishing."
                            if target_clip.get("deleted_from_telegram")
                            else "⚠️ Instagram published successfully, but Telegram cleanup failed."
                        )
                    )
                )
            return
        except Exception as e:
            target_clip["status"] = "FAILED"
            target_clip["instagram_status"] = "FAILED"
            try:
                await save_queue_manifest(manifest_message, queue)
            except Exception:
                pass
            print(
                "❌ Legacy Instagram publishing failed: "
                f"{type(e).__name__}: {str(e)}"
            )
            return


async def process_pending_queues():
    """Serialize background and manual Instagram queue publishing."""
    async with queue_publish_lock:
        return await _process_pending_queues()


async def get_last_upload_reminder_time():
    """Return the timestamp of the newest upload reminder in the storage channel."""
    storage_channel = await find_storage_channel()
    if storage_channel is None:
        return None

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=200
    )

    for message in messages:
        text = message.message or ""
        if not text.startswith(UPLOAD_REMINDER_MARKER):
            continue

        try:
            payload = json.loads(text.split("\n", 1)[1])
            value = payload.get("sent_at")
            if not value:
                continue

            timestamp = datetime.fromisoformat(
                value.replace("Z", "+00:00")
            )
            if timestamp.tzinfo is None:
                timestamp = timestamp.replace(tzinfo=timezone.utc)
            return timestamp
        except Exception:
            continue

    return None


async def storage_channel_is_idle(manifests):
    """Return True when no title/processing/publishing work is pending."""

    if await load_title_request():
        return False

    storage_channel = await find_storage_channel()
    if storage_channel is None:
        return False

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=200
    )

    for message in messages:
        text = message.message or ""
        if text.startswith(PROCESSING_MARKER):
            return False

    for item in manifests:
        queue = item.get("queue", {})
        if queue.get("status") == "COMPLETED":
            continue

        if not queue.get("processing_complete", False):
            return False

        if queue.get("queue_version") == 2 and "clip_message_ids" in queue:
            if int(queue.get("next_clip_index", 1)) <= int(queue.get("total_clips", 0)):
                return False
        else:
            for clip in queue.get("clips", []):
                if clip.get("instagram_status") != "PUBLISHED":
                    return False

    return True


async def maybe_send_upload_reminder(manifests):
    """Send an upload prompt to the private storage channel every hour while idle."""
    if not await storage_channel_is_idle(manifests):
        return

    storage_channel = await find_storage_channel()
    if storage_channel is None:
        return

    now = datetime.now(timezone.utc)
    last_reminder = await get_last_upload_reminder_time()

    if last_reminder is not None:
        elapsed = (now - last_reminder).total_seconds()
        if elapsed < UPLOAD_REMINDER_INTERVAL_SECONDS:
            return

    payload = {
        "sent_at": now.isoformat()
    }

    text = (
        f"{UPLOAD_REMINDER_MARKER}\n"
        f"{json.dumps(payload)}\n\n"
        "📥 READY FOR THE NEXT VIDEO\n\n"
        "Upload the ORIGINAL video to this channel.\n"
        "Then reply to the bot with the title.\n\n"
        "🎬 After that, everything is automatic."
    )

    await telethon_client.send_message(
        storage_channel,
        text
    )

    print("📥 Upload reminder sent to the storage channel.")


async def instagram_queue_loop():
    """
    Background loop for the Instagram queue.

    The worker checks every minute, but the persistent cooldown above
    allows only ONE successful Reel publication every configured interval.
    The daily publishing window is temporarily disabled for testing.
    """
    await asyncio.sleep(15)

    while True:
        try:
            manifests = await find_queue_manifests()
            await process_pending_queues()
            # If nothing is waiting to publish, remind the user in the
            # private storage channel every hour to upload the next video.
            await maybe_send_upload_reminder(manifests)
        except Exception as e:
            print(
                "❌ Instagram queue loop error:\n"
                f"{type(e).__name__}: {str(e)}"
            )

        # Check frequently so the next Reel is posted close to the
        # exact one-hour mark without publishing more than one per hour.
        await asyncio.sleep(60)



# ============================================================
# PROCESS ORIGINAL VIDEO
# ============================================================

async def process_original_video(
    video_message_id,
    title,
    admin_chat_id
):

    storage_channel = (
        await find_storage_channel()
    )

    if storage_channel is None:

        raise RuntimeError(
            f'Could not find "{STORAGE_CHANNEL_NAME}".'
        )

    await save_processing_state(
        video_message_id,
        title
    )

    temp_directory = tempfile.mkdtemp(
        prefix="cartoon_bot_"
    )

    queue = None
    manifest_message = None
    uploaded_messages = []
    processing_complete = False

    try:

        # ----------------------------------------------------
        # Find original
        # ----------------------------------------------------

        print(
            f"Looking for original video "
            f"message ID {video_message_id}"
        )

        original_message = (
            await telethon_client.get_messages(
                storage_channel,
                ids=video_message_id
            )
        )

        if not original_message:

            raise RuntimeError(
                "Original video message could not be found."
            )

        if not original_message.video:

            raise RuntimeError(
                "The stored message is not a video."
            )

        # ----------------------------------------------------
        # Download original
        # ----------------------------------------------------

        original_path = os.path.join(
            temp_directory,
            "original.mp4"
        )

        progress_message = await bot_application.bot.send_message(
            chat_id=admin_chat_id,
            text=(
                "⏳ PROCESSING STARTED\n\n"
                f"🎬 {title}\n\n"
                "📥 Downloading original video..."
            )
        )

        progress_reporter = TelegramProgressReporter(
            bot_application.bot,
            admin_chat_id,
            progress_message.message_id,
            min_interval=2.0,
        )

        print("Downloading original...")

        download_started = time.monotonic()

        def download_progress(current, total):
            if not total:
                return
            percent = (current / total) * 100.0
            elapsed = max(0.01, time.monotonic() - download_started)
            speed = current / elapsed
            remaining_bytes = max(0, total - current)
            eta = remaining_bytes / speed if speed > 0 else 0
            progress_reporter.schedule(
                "📥 DOWNLOADING ORIGINAL\n\n"
                f"🎬 {title}\n\n"
                f"{progress_bar(percent)} {percent:5.1f}%\n\n"
                f"📦 {current / 1024 / 1024:.1f} / {total / 1024 / 1024:.1f} MB\n"
                f"⚡ {speed / 1024 / 1024:.2f} MB/s\n"
                f"⏳ ETA: ~{format_duration(eta)}"
            )

        downloaded_path = await download_original_when_ready(
            video_message_id,
            original_path,
            progress_callback=download_progress,
        )

        if not downloaded_path:
            raise RuntimeError(
                "Failed to download original video."
            )

        # ----------------------------------------------------
        # FAST STREAM-COPY SPLIT + IMMEDIATE TELEGRAM UPLOAD
        # ----------------------------------------------------
        clips_directory = os.path.join(temp_directory, "clips")
        os.makedirs(clips_directory, exist_ok=True)

        await progress_reporter.edit(
            "✂️ FAST SPLITTING + UPLOADING\n\n"
            f"🎬 {title}\n\n"
            "⚡ Stream copy (no re-encoding)\n"
            "📤 Each clip will be uploaded as soon as it is ready.\n"
            "⏳ Instagram publishing starts after ALL clips are ready.",
            force=True,
        )

        # Create the persistent queue BEFORE the splitter starts producing
        # clips. Instagram publishing remains blocked until processing_complete
        # is set to True after all clips are split and uploaded.
        queue, manifest_message = await create_automatic_queue(
            storage_channel,
            title,
            video_message_id,
            [],
        )
        queue["processing_complete"] = False
        queue["total_clips"] = 0
        queue["clip_message_ids"] = []
        await save_queue_manifest(manifest_message, queue)

        uploaded_messages = []
        uploaded_count = 0
        splitter_done = False
        seen_files = set()

        async def upload_ready_clip(clip_path):
            nonlocal uploaded_count
            index = uploaded_count + 1
            filename = f"{safe_filename(title)} Part {index}.mp4"
            final_path = os.path.join(clips_directory, filename)
            if os.path.abspath(clip_path) != os.path.abspath(final_path):
                os.replace(clip_path, final_path)

            caption = (
                f"{CLIP_MARKER}\n"
                f"Title: {title}\n"
                f"Part: {index}"
            )
            clip_size = os.path.getsize(final_path)
            upload_started = time.monotonic()

            def upload_progress(current, total):
                total_bytes = total or clip_size
                percent = (current / total_bytes) * 100.0 if total_bytes else 0.0
                elapsed = max(0.01, time.monotonic() - upload_started)
                speed = current / elapsed
                remaining_bytes = max(0, total_bytes - current)
                eta = remaining_bytes / speed if speed > 0 else 0
                progress_reporter.schedule(
                    "📤 UPLOADING READY CLIP\n\n"
                    f"🎬 {title}\n\n"
                    f"📦 Part {index}\n"
                    f"{progress_bar(percent, 16)} {percent:5.1f}%\n"
                    f"💾 {current / 1024 / 1024:.1f} / {total_bytes / 1024 / 1024:.1f} MB\n"
                    f"⚡ {speed / 1024 / 1024:.2f} MB/s\n"
                    f"⏳ ETA: ~{format_duration(eta)}"
                )

            # Upload the bytes first using the maximum supported Telegram
            # chunk size, then send the uploaded handle. This avoids the
            # smaller/default upload chunk sizing used by the high-level path.
            uploaded_file = await telethon_client.upload_file(
                final_path,
                part_size_kb=TELEGRAM_TRANSFER_PART_SIZE_KB,
                file_size=clip_size,
                progress_callback=upload_progress,
            )

            # Preserve the .mp4 filename so Telethon sends this as video media.
            try:
                uploaded_file.name = os.path.basename(final_path)
            except Exception:
                pass

            uploaded_message = await telethon_client.send_file(
                storage_channel,
                uploaded_file,
                caption=caption,
                force_document=False,
                supports_streaming=True,
            )
            if isinstance(uploaded_message, list):
                if not uploaded_message:
                    raise RuntimeError(f"Upload returned no message for Part {index}.")
                uploaded_message = uploaded_message[0]

            uploaded_messages.append(uploaded_message)
            uploaded_count += 1
            await append_clip_to_queue(
                manifest_message, queue, uploaded_message, title, index
            )
            print(f"Uploaded Part {index}: Telegram message ID {uploaded_message.id}; added to live queue.")

        # Run FFmpeg segmentation once. While it runs, watch for finalized
        # segment files and upload them immediately.
        async def run_stream_splitter():
            # Find keyframes first so every non-final segment ends at a keyframe
            # no later than 60 seconds. This preserves the fast -c copy path.
            probe = [
                "ffprobe", "-v", "error", "-skip_frame", "nokey",
                "-select_streams", "v:0",
                "-show_entries", "frame=best_effort_timestamp_time",
                "-of", "csv=p=0", original_path,
            ]
            probe_proc = await asyncio.create_subprocess_exec(
                *probe, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            probe_out, probe_err = await probe_proc.communicate()
            if probe_proc.returncode != 0:
                raise RuntimeError(
                    "Could not read video keyframes.\n"
                    + probe_err.decode(errors="replace")[-2000:]
                )

            keyframes = []
            for line in probe_out.decode(errors="replace").splitlines():
                try:
                    value = float(line.strip())
                    if value >= 0:
                        keyframes.append(value)
                except ValueError:
                    pass
            if not keyframes:
                raise RuntimeError("No video keyframes were found.")

            duration = await get_video_duration(original_path)
            boundaries = []
            current = 0.0
            while duration - current > 60.0:
                candidates = [
                    k for k in keyframes
                    if current + 45.0 <= k <= current + 60.0
                ]
                if not candidates:
                    raise RuntimeError(
                        f"No safe keyframe between {current + 45:.1f}s and {current + 60:.1f}s. "
                        "Cannot create a stream-copy clip that stays within 60 seconds."
                    )
                boundary = min(candidates, key=lambda k: abs(k - (current + 60.0)))
                boundaries.append(boundary)
                current = boundary

            command = [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                "-i", original_path,
                "-map", "0:v:0", "-map", "0:a:0?",
                "-c", "copy",
                "-f", "segment",
                "-segment_times", ",".join(f"{x:.3f}" for x in boundaries),
                "-reset_timestamps", "1",
                "-segment_format", "mp4",
                os.path.join(clips_directory, "part_%03d.mp4"),
            ]
            print("Running FAST stream-copy FFmpeg:")
            print(" ".join(command))
            proc = await asyncio.create_subprocess_exec(
                *command,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            return proc, asyncio.create_task(proc.stderr.read()), duration, boundaries

        process, stderr_task, source_duration, boundaries = await run_stream_splitter()
        wait_task = asyncio.create_task(process.wait())
        while not wait_task.done():
            current_files = sorted(
                os.path.join(clips_directory, name)
                for name in os.listdir(clips_directory)
                if name.startswith("part_") and name.endswith(".mp4")
            )
            for clip_path in current_files:
                if clip_path in seen_files:
                    continue
                # FFmpeg may still be closing a segment; wait until its size
                # is stable before uploading it.
                size1 = os.path.getsize(clip_path)
                await asyncio.sleep(0.4)
                if not os.path.isfile(clip_path):
                    continue
                size2 = os.path.getsize(clip_path)
                if size1 != size2 or size2 == 0:
                    continue
                seen_files.add(clip_path)
                await upload_ready_clip(clip_path)

            await asyncio.sleep(0.5)

        return_code = await wait_task
        stderr = await stderr_task
        if return_code != 0:
            raise RuntimeError(
                "FFmpeg failed to split the video.\n"
                + stderr.decode(errors="replace")[-2000:]
            )

        # Pick up the final segment after FFmpeg closes the file.
        for clip_path in sorted(
            os.path.join(clips_directory, name)
            for name in os.listdir(clips_directory)
            if name.startswith("part_") and name.endswith(".mp4")
        ):
            if clip_path not in seen_files:
                seen_files.add(clip_path)
                await upload_ready_clip(clip_path)

        if not uploaded_messages:
            raise RuntimeError("FFmpeg completed but produced no uploaded clips.")

        # Mark the live queue as fully generated only after FFmpeg and all
        # Telegram uploads have completed. Instagram publishing starts only
        # after this flag becomes True.
        queue["processing_complete"] = True
        queue["total_clips"] = len(uploaded_messages)
        await save_queue_manifest(manifest_message, queue)
        processing_complete = True

        print(f"FAST split/upload complete: {len(uploaded_messages)} clips.")

        # ----------------------------------------------------
        # SAFETY CHECK
        # ----------------------------------------------------
        if not uploaded_messages:
            raise RuntimeError("No clips were uploaded. Original will NOT be deleted.")

        print(f"Live queue contains {len(uploaded_messages)} uploaded clips.")
        print(f"Manifest message ID: {manifest_message.id}")

        # ----------------------------------------------------
        # ONLY NOW delete original
        # ----------------------------------------------------

        print(
            "All clips successfully uploaded."
        )

        print(
            "Deleting original video..."
        )

        await telethon_client.delete_messages(
            storage_channel,
            video_message_id
        )

        print(
            "Original video deleted."
        )

        # ----------------------------------------------------
        # Cleanup state
        # ----------------------------------------------------

        await delete_title_request()
        await delete_processing_state()

        # ----------------------------------------------------
        # Notify user
        # ----------------------------------------------------

        await progress_reporter.edit(
            "✅ VIDEO PROCESSING COMPLETE!\n\n"
            f"🎬 {title}\n\n"
            f"✂️ Parts created: {len(uploaded_messages)}\n"
            "📤 All parts uploaded to Telegram\n"
            "🗑️ Original video deleted\n\n"
            "📋 Instagram queue created.\n"
            "⏳ Waiting for automatic Instagram publishing.",
            force=True,
        )

    except Exception as e:

        print(
            "❌ VIDEO PROCESSING FAILED"
        )

        print(
            f"{type(e).__name__}: {str(e)}"
        )

        # Processing failed before the queue became publishable. Remove only
        # clips generated by this attempt and its queue manifest. The original
        # video is deliberately kept in Telegram for safety.
        if not processing_complete:
            for uploaded_message in uploaded_messages:
                try:
                    await telethon_client.delete_messages(
                        storage_channel,
                        uploaded_message.id
                    )
                except Exception as cleanup_error:
                    print(
                        "⚠️ Could not delete partial generated clip "
                        f"{uploaded_message.id}: "
                        f"{type(cleanup_error).__name__}: {str(cleanup_error)}"
                    )

            if manifest_message is not None:
                try:
                    await telethon_client.delete_messages(
                        storage_channel,
                        manifest_message.id
                    )
                except Exception as cleanup_error:
                    print(
                        "⚠️ Could not delete failed queue manifest: "
                        f"{type(cleanup_error).__name__}: {str(cleanup_error)}"
                    )

        try:
            await delete_title_request()
        except Exception:
            pass

        try:
            await delete_processing_state()
        except Exception:
            pass

        try:
            await bot_application.bot.send_message(
                chat_id=admin_chat_id,
                text=(
                    "❌ VIDEO PROCESSING FAILED\n\n"
                    f"🎬 {title}\n\n"
                    f"Error: {type(e).__name__}\n"
                    f"{str(e)}\n\n"
                    "⚠️ The original video was NOT deleted.\n"
                    f"Your video is still safe in {STORAGE_CHANNEL_NAME}.\n\n"
                    + (
                        "Generated partial clips from this failed processing "
                        "attempt were cleaned up."
                        if not processing_complete
                        else "The completed Instagram queue was preserved."
                    )
                )
            )
        except Exception as notify_error:
            print(
                "⚠️ Could not send processing failure notification: "
                f"{type(notify_error).__name__}: {str(notify_error)}"
            )

    finally:

        # Delete temporary Render files.
        try:

            shutil.rmtree(
                temp_directory,
                ignore_errors=True
            )

        except Exception:
            pass


# ============================================================
# CHANNEL VIDEO DETECTOR
# ============================================================

async def channel_video_handler(event):

    global pending_video_message_id

    try:

        message = event.message

        if not message.video:
            return

        caption = message.message or ""

        # Ignore generated clips.
        if caption.startswith(
            CLIP_MARKER
        ):
            return

        # Ignore queue manifests.
        if caption.startswith(
            QUEUE_MARKER
        ):
            return

        # Ignore configuration.
        if caption.startswith(
            CONFIG_MARKER
        ):
            return

        # Ignore title state.
        if caption.startswith(
            TITLE_REQUEST_MARKER
        ):
            return

        # Ignore processing state.
        if caption.startswith(
            PROCESSING_MARKER
        ):
            return

        print(
            "🎬 NEW ORIGINAL VIDEO DETECTED"
        )

        print(
            f"Telegram message ID: {message.id}"
        )

        chat_id = await load_admin_chat_id()

        if not chat_id:

            print(
                "⚠️ Admin chat ID not found."
            )

            print(
                "Send /start to the bot first."
            )

            return

        # Never replace an active processing job or pending title request.
        processing_state = await load_processing_state()
        if processing_state:
            await bot_application.bot.send_message(
                chat_id=chat_id,
                text=(
                    "⏳ A video is already being processed.\n\n"
                    f"🎬 {processing_state.get('title', 'Current video')}\n"
                    "Please wait until it finishes."
                )
            )
            return

        existing_title_request = await load_title_request()
        if existing_title_request:
            await bot_application.bot.send_message(
                chat_id=chat_id,
                text=(
                    "⏳ A video is already waiting for a title.\n\n"
                    f"Telegram video ID: {existing_title_request}\n"
                    "Please send its title first."
                )
            )
            return

        await save_title_request(
            message.id
        )

        pending_video_message_id = (
            message.id
        )

        await send_title_question(
            chat_id,
            message.id
        )

    except Exception as e:

        print(
            "❌ CHANNEL VIDEO HANDLER ERROR:"
        )

        print(
            f"{type(e).__name__}: {str(e)}"
        )


# ============================================================
# SEND TITLE QUESTION
# ============================================================

async def send_title_question(
    chat_id,
    video_message_id
):

    try:

        await bot_application.bot.send_message(
            chat_id=chat_id,
            text=(
                "🎬 NEW VIDEO DETECTED!\n\n"
                f"Telegram video ID: {video_message_id}\n\n"
                "✏️ What is the title of this video?\n\n"
                "Example:\n"
                "Doraemon Episode 25"
            )
        )

    except Exception as e:

        print(
            "❌ Could not send title question:"
        )

        print(
            f"{type(e).__name__}: {str(e)}"
        )


# ============================================================
# TITLE RESPONSE
# ============================================================

async def handle_title(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    global pending_video_message_id

    if not update.message:
        return

    title = (
        update.message.text or ""
    ).strip()

    if not title:
        return

    if title.startswith("/"):
        return

    chat_id = update.effective_chat.id

    saved_chat_id = (
        await load_admin_chat_id()
    )

    if saved_chat_id != chat_id:
        return

    video_message_id = (
        await load_title_request()
    )

    if not video_message_id:

        await update.message.reply_text(
            "ℹ️ I don't have a video waiting "
            "for a title."
        )

        return

    pending_video_message_id = (
        video_message_id
    )

    print(
        "🎬 TITLE RECEIVED"
    )

    print(
        f"Title: {title}"
    )

    print(
        f"Video message ID: "
        f"{video_message_id}"
    )

    await update.message.reply_text(
        "✅ Title received!\n\n"
        f"🎬 {title}\n\n"
        "🚀 Starting automatic processing..."
    )

    # Start processing.
    #
    # We await it here so the job is tracked by
    # the Telegram bot event loop.
    await process_original_video(
        video_message_id,
        title,
        chat_id
    )

async def publish_queue_now(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    chat_id = update.effective_chat.id
    saved_chat_id = await load_admin_chat_id()

    if saved_chat_id != chat_id:
        return

    await update.message.reply_text(
        "🚀 Starting Instagram queue check..."
    )

    await process_pending_queues()

    await update.message.reply_text(
        "✅ Instagram queue check finished."
    )



async def test_public_url(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    chat_id = update.effective_chat.id
    saved_chat_id = await load_admin_chat_id()

    if saved_chat_id != chat_id:
        return

    if not PUBLIC_BASE_URL:
        await update.message.reply_text(
            "❌ PUBLIC_BASE_URL is missing in Render."
        )
        return

    try:
        url = f"{PUBLIC_BASE_URL}/health"

        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": "Cartoon-Instagram-Bot/1.0"
            },
            method="GET"
        )

        with urllib.request.urlopen(
            request,
            timeout=30
        ) as response:
            body = response.read().decode("utf-8", errors="replace")

        await update.message.reply_text(
            "✅ PUBLIC URL WORKS!\n\n"
            f"URL: {PUBLIC_BASE_URL}\n"
            f"HTTP status: {response.status}\n"
            f"Response: {body}"
        )

    except Exception as e:
        await update.message.reply_text(
            "❌ PUBLIC URL TEST FAILED\n\n"
            f"{type(e).__name__}: {str(e)}"
        )




# ============================================================
# SHOW QUEUE
# ============================================================

async def show_queue(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    try:

        storage_channel = (
            await find_storage_channel()
        )

        if storage_channel is None:

            raise RuntimeError(
                f'Could not find "{STORAGE_CHANNEL_NAME}".'
            )

        messages = await telethon_client.get_messages(
            storage_channel,
            limit=100
        )

        manifest = None

        for message in messages:

            text = message.message or ""

            if text.startswith(
                QUEUE_MARKER
            ):

                manifest = message
                break

        if manifest is None:

            await update.message.reply_text(
                "📋 No queue manifest exists yet."
            )

            return

        text = manifest.message

        if len(text) > 3500:
            text = text[:3500]

        await update.message.reply_text(
            "📋 CURRENT QUEUE\n\n"
            + text
        )

    except Exception as e:

        await update.message.reply_text(
            "❌ Could not read queue.\n\n"
            f"Error: {type(e).__name__}\n"
            f"Details: {str(e)}"
        )


# ============================================================
# BOT VIDEO HANDLER
# ============================================================

async def handle_video(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    if not update.message:
        return

    if not update.message.video:
        return

    await update.message.reply_text(
        "📥 Video received by the bot.\n\n"
        "Please upload the ORIGINAL video "
        f"directly into {STORAGE_CHANNEL_NAME}."
    )


# ============================================================
# MAIN
# ============================================================

async def application_post_init(application):
    """
    Start the Instagram queue worker after python-telegram-bot
    has initialized its asyncio event loop.
    """
    application.create_task(
        instagram_queue_loop(),
        update=None
    )


def main():

    global telethon_client
    global bot_application

    if not BOT_TOKEN:
        raise RuntimeError(
            "BOT_TOKEN is missing."
        )

    if not API_ID:
        raise RuntimeError(
            "API_ID is missing."
        )

    if not API_HASH:
        raise RuntimeError(
            "API_HASH is missing."
        )

    if not TELEGRAM_SESSION:
        raise RuntimeError(
            "TELEGRAM_SESSION is missing."
        )

    # Instagram credentials are intentionally checked by
    # /test_instagram so the existing Telegram pipeline can
    # still start while Instagram setup is being verified.

    # --------------------------------------------------------
    # Health server
    # --------------------------------------------------------

    health_thread = threading.Thread(
        target=start_health_server,
        daemon=True,
    )

    health_thread.start()

    # --------------------------------------------------------
    # Telethon
    # --------------------------------------------------------

    telethon_client = TelegramClient(
        StringSession(TELEGRAM_SESSION),
        API_ID,
        API_HASH,
    )

    telethon_client.start()

    print(
        "Telethon connected successfully."
    )

    # --------------------------------------------------------
    # Telegram Bot API
    # --------------------------------------------------------

    bot_application = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(application_post_init)
        .build()
    )

    bot_application.add_handler(
        CommandHandler(
            "start",
            start
        )
    )

    bot_application.add_handler(
        CommandHandler(
            "test_telegram",
            test_telegram
        )
    )

    bot_application.add_handler(
        CommandHandler(
            "test_instagram",
            test_instagram
        )
    )

    bot_application.add_handler(
        CommandHandler(
            "queue",
            show_queue
        )
    )

    bot_application.add_handler(
        CommandHandler(
            "publish_queue",
            publish_queue_now
        )
    )

    bot_application.add_handler(
        CommandHandler(
            "test_public_url",
            test_public_url
        )
    )

    bot_application.add_handler(
        MessageHandler(
            filters.VIDEO,
            handle_video
        )
    )

    bot_application.add_handler(
        MessageHandler(
            filters.TEXT
            & ~filters.COMMAND,
            handle_title
        )
    )

    # --------------------------------------------------------
    # Telethon channel watcher
    # --------------------------------------------------------

    @telethon_client.on(
        events.NewMessage()
    )
    async def new_telegram_message(event):

        try:

            chat = await event.get_chat()

            title = getattr(
                chat,
                "title",
                None
            )

            if title != STORAGE_CHANNEL_NAME:
                return

            await channel_video_handler(
                event
            )

        except Exception as e:

            print(
                "❌ Telegram event error:"
            )

            print(
                f"{type(e).__name__}: {str(e)}"
            )

    # --------------------------------------------------------
    # Start
    # --------------------------------------------------------

    print(
        f"Bot is running. "
        f"Health server listening on port {PORT}."
    )
    print(
        "Instagram posting interval: "
        f"{INSTAGRAM_POST_INTERVAL_SECONDS} seconds "
        "(configured seconds)."
    )
    print(
        "Upload reminder interval: "
        f"{UPLOAD_REMINDER_INTERVAL_SECONDS} seconds "
        "(minimum 1 hour)."
    )

    bot_application.run_polling(
        close_loop=False
    )


# ============================================================
# ENTRY POINT
# ============================================================

if __name__ == "__main__":
    main()
