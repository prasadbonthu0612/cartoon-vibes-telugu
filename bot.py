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

from telegram import Update, BotCommand
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
# Default is disabled to preserve the existing 24/7 test behavior.
# Use /window 06:00 21:00 to enable a publishing window.
INSTAGRAM_TIMEZONE = ZoneInfo("Asia/Kolkata")
INSTAGRAM_PUBLISH_START_HOUR = 6
INSTAGRAM_PUBLISH_END_HOUR = 21

# Send a reminder in the private Telegram storage channel when the bot is idle.
# Default is one hour; Telegram command /reminder can increase it.
# The interval is never allowed below one hour.
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

# Persistent Telegram-controlled bot settings.
DEFAULT_BOT_SETTINGS = {
    "window_enabled": False,
    "window_start_minutes": 6 * 60,
    "window_end_minutes": 21 * 60,
    "interval_seconds": INSTAGRAM_POST_INTERVAL_SECONDS,
    "reminder_seconds": 3600,
    "publishing_paused": False,
    "notifications": {
        "processing_complete": True,
        "processing_failed": True,
        "published": True,
        "publish_failed": True,
        "queue_complete": True,
        "upload_reminder": True,
    },
}

bot_settings = json.loads(json.dumps(DEFAULT_BOT_SETTINGS))

# The task currently processing an original video, if any.
current_processing_task = None

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
# PERSISTENT BOT CONFIGURATION
# ============================================================

def _default_bot_settings():
    return json.loads(json.dumps(DEFAULT_BOT_SETTINGS))


def _apply_bot_settings(settings):
    """Apply persisted Telegram-controlled settings to runtime globals."""
    global INSTAGRAM_POST_INTERVAL_SECONDS
    global UPLOAD_REMINDER_INTERVAL_SECONDS
    global INSTAGRAM_PUBLISH_START_HOUR
    global INSTAGRAM_PUBLISH_END_HOUR

    merged = _default_bot_settings()
    if isinstance(settings, dict):
        for key in (
            "window_enabled",
            "window_start_minutes",
            "window_end_minutes",
            "interval_seconds",
            "reminder_seconds",
            "publishing_paused",
        ):
            if key in settings:
                merged[key] = settings[key]

        saved_notifications = settings.get("notifications")
        if isinstance(saved_notifications, dict):
            merged["notifications"].update(saved_notifications)

    try:
        merged["window_start_minutes"] = int(merged["window_start_minutes"]) % (24 * 60)
        merged["window_end_minutes"] = int(merged["window_end_minutes"]) % (24 * 60)
        merged["interval_seconds"] = max(60, int(merged["interval_seconds"]))
        merged["reminder_seconds"] = max(3600, int(merged["reminder_seconds"]))
    except (TypeError, ValueError):
        merged = _default_bot_settings()

    bot_settings.clear()
    bot_settings.update(merged)

    INSTAGRAM_POST_INTERVAL_SECONDS = merged["interval_seconds"]
    UPLOAD_REMINDER_INTERVAL_SECONDS = merged["reminder_seconds"]

    start_minutes = merged["window_start_minutes"]
    end_minutes = merged["window_end_minutes"]
    INSTAGRAM_PUBLISH_START_HOUR = start_minutes // 60
    INSTAGRAM_PUBLISH_END_HOUR = end_minutes // 60

    return merged


async def load_bot_config():
    """Load persistent bot settings from the single CONFIG_MARKER message."""
    global admin_chat_id

    storage_channel = await find_storage_channel()
    if storage_channel is None:
        return _apply_bot_settings(bot_settings)

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:
        text = message.message or ""
        if not text.startswith(CONFIG_MARKER):
            continue

        try:
            config = json.loads(text.split("\n", 1)[1])

            if config.get("admin_chat_id") is not None:
                admin_chat_id = config.get("admin_chat_id")

            saved_settings = config.get("settings", {})
            if isinstance(saved_settings, dict):
                return _apply_bot_settings(saved_settings)

        except Exception as e:
            print(
                f"⚠️ Could not load bot configuration from message "
                f"{message.id}: {type(e).__name__}: {str(e)}"
            )

    return _apply_bot_settings(bot_settings)


async def save_bot_config():
    """Persist admin ID and all Telegram-controlled settings in one message."""
    storage_channel = await find_storage_channel()

    if storage_channel is None:
        raise RuntimeError(
            f'Could not find "{STORAGE_CHANNEL_NAME}".'
        )

    config = {
        "admin_chat_id": admin_chat_id,
        "settings": bot_settings,
    }

    config_json = json.dumps(
        config,
        ensure_ascii=False,
        separators=(",", ":")
    )

    config_text = (
        f"{CONFIG_MARKER}\n"
        f"{config_json}"
    )

    if len(config_text) > 3500:
        raise RuntimeError(
            "Bot configuration unexpectedly exceeded Telegram message limits."
        )

    messages = await telethon_client.get_messages(
        storage_channel,
        limit=100
    )

    for message in messages:
        text = message.message or ""
        if text.startswith(CONFIG_MARKER):
            await safe_telethon_edit_message(
                storage_channel,
                message.id,
                config_text
            )
            return

    await telethon_client.send_message(
        storage_channel,
        config_text
    )


async def save_admin_chat_id(chat_id):
    global admin_chat_id

    admin_chat_id = chat_id
    await save_bot_config()


async def load_admin_chat_id():
    global admin_chat_id

    if admin_chat_id:
        return admin_chat_id

    await load_bot_config()
    return admin_chat_id


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


def publish_reel_from_file(
    file_path,
    title,
    part_index,
    total_parts,
    progress_callback=None,
):
    """Publish one Reel while optionally reporting live Instagram progress."""
    token = None

    def report(phase, phase_percent, overall_percent, details):
        if progress_callback:
            progress_callback(phase, phase_percent, overall_percent, details)

    try:
        report(
            "PREPARING INSTAGRAM REEL",
            0.0,
            20.0,
            f"📦 Part {part_index}/{total_parts}\n"
            "🌐 Registering temporary public media URL...",
        )

        token, public_url = register_public_media(file_path)

        caption = build_instagram_caption(
            title,
            part_index,
            total_parts
        )

        report(
            "CREATING INSTAGRAM CONTAINER",
            50.0,
            27.0,
            f"📦 Part {part_index}/{total_parts}\n"
            "📤 Sending Reel container request to Instagram...\n"
            "📐 Type: REELS\n"
            "📲 Share to feed: true",
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
                "share_to_feed": "true",
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

        report(
            "INSTAGRAM VIDEO PROCESSING",
            0.0,
            30.0,
            f"📦 Part {part_index}/{total_parts}\n"
            f"🆔 Container: {creation_id}\n"
            "📡 Instagram is downloading/transcoding the Reel...",
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

            poll_percent = (attempt / max_attempts) * 100.0
            overall = 30.0 + (50.0 * poll_percent / 100.0)
            report(
                "INSTAGRAM VIDEO PROCESSING",
                poll_percent,
                overall,
                f"📦 Part {part_index}/{total_parts}\n"
                f"🆔 Container: {creation_id}\n"
                f"📡 Status: {status_code or 'PROCESSING'}\n"
                f"🔎 Check: {attempt}/{max_attempts}\n"
                f"⏳ Poll interval: {poll_seconds}s",
            )

            if status_code == "FINISHED":
                report(
                    "INSTAGRAM VIDEO READY",
                    100.0,
                    80.0,
                    f"📦 Part {part_index}/{total_parts}\n"
                    f"🆔 Container: {creation_id}\n"
                    "✅ Instagram finished processing the video.",
                )
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

        report(
            "PUBLISHING TO INSTAGRAM",
            50.0,
            90.0,
            f"📦 Part {part_index}/{total_parts}\n"
            f"🆔 Container: {creation_id}\n"
            "🚀 Sending media_publish request...",
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

        report(
            "INSTAGRAM PUBLISHED",
            100.0,
            100.0,
            f"📦 Part {part_index}/{total_parts}\n"
            f"🆔 Instagram Media ID: {media_id}\n"
            "✅ Publication confirmed by Instagram.",
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
    if not await command_is_admin(update):
        return

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
    if not await command_is_admin(update):
        return


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
# INSTAGRAM REEL PORTRAIT FORMAT
# ============================================================

async def format_clip_for_reels(
    input_path,
    output_path,
    progress_reporter=None,
    title="Video",
    part_index=1,
    total_parts=1,
    overall_start=25.0,
    overall_span=0.0,
    workflow_started=None,
    completed=None,
):
    """Convert one split clip to 1080x1920 while reporting live FFmpeg progress."""
    if not os.path.isfile(input_path):
        raise RuntimeError(f"Clip does not exist: {input_path}")

    if os.path.abspath(input_path) == os.path.abspath(output_path):
        raise RuntimeError("Portrait formatting requires a separate output file.")

    os.makedirs(os.path.dirname(output_path) or ".", exist_ok=True)
    duration = await get_video_duration(input_path)
    started = workflow_started or time.monotonic()

    command = [
        "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
        "-i", input_path,
        "-map", "0:v:0",
        "-map", "0:a:0?",
        "-vf",
        "scale=1080:1920:force_original_aspect_ratio=decrease,"
        "pad=1080:1920:(ow-iw)/2:(oh-ih)/2:color=black",
        "-c:v", "libx264",
        "-preset", "veryfast",
        "-crf", "23",
        "-c:a", "aac",
        "-b:a", "128k",
        "-movflags", "+faststart",
        "-progress", "pipe:1",
        output_path,
    ]

    print("📱 Formatting clip for Instagram portrait Reel:")
    print(" ".join(command))

    process = await asyncio.create_subprocess_exec(
        *command,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )

    def on_progress(percent, processed_seconds, ffmpeg_speed):
        if not progress_reporter:
            return

        elapsed = max(0.01, time.monotonic() - started)
        if processed_seconds > 0:
            remaining = max(0.0, duration - processed_seconds)
            eta = remaining * elapsed / processed_seconds
        else:
            eta = None

        overall = overall_start + (overall_span * percent / 100.0)
        details = (
            f"🎞️ Part {part_index}/{total_parts}\n"
            f"🎨 Portrait conversion: {percent:5.1f}%\n"
            f"⏱️ Encoded: {format_duration(processed_seconds)} / {format_duration(duration)}\n"
            f"⚡ FFmpeg speed: {ffmpeg_speed or 'working'}"
        )
        progress_reporter.schedule(
            build_live_processing_report(
                title,
                f"PORTRAIT FORMAT — Part {part_index}/{total_parts}",
                percent,
                overall,
                elapsed,
                eta,
                details,
                completed,
            )
        )

    progress_task = asyncio.create_task(
        monitor_ffmpeg_progress(process.stdout, duration, on_progress)
    )
    stderr = await process.stderr.read()
    return_code = await process.wait()
    await progress_task

    if return_code != 0:
        error_text = stderr.decode(errors="replace").strip()
        raise RuntimeError(
            "FFmpeg failed to format the clip for Instagram.\n"
            f"{error_text[-2000:]}"
        )

    if not os.path.isfile(output_path) or os.path.getsize(output_path) == 0:
        raise RuntimeError(
            "FFmpeg completed but produced no usable portrait Reel clip."
        )

    if progress_reporter:
        elapsed = max(0.01, time.monotonic() - started)
        progress_reporter.schedule(
            build_live_processing_report(
                title,
                f"PORTRAIT FORMAT — Part {part_index}/{total_parts}",
                100.0,
                overall_start + overall_span,
                elapsed,
                0,
                (
                    f"🎞️ Part {part_index}/{total_parts}\n"
                    "🎨 Portrait conversion: 100.0%\n"
                    "📐 Output: 1080×1920\n"
                    f"💾 Output: {os.path.getsize(output_path) / 1024 / 1024:.1f} MB"
                ),
                completed,
            )
        )

    return output_path


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


def format_rate(bytes_per_second):
    if not bytes_per_second or bytes_per_second <= 0:
        return "--"
    if bytes_per_second >= 1024 * 1024:
        return f"{bytes_per_second / 1024 / 1024:.2f} MB/s"
    return f"{bytes_per_second / 1024:.0f} KB/s"


def format_eta(seconds):
    if seconds is None or seconds <= 0:
        return "--"
    return f"~{format_duration(seconds)}"


def build_live_processing_report(
    title,
    phase,
    phase_percent,
    overall_percent,
    elapsed,
    eta=None,
    details=None,
    completed=None,
):
    """Build the live Telegram processing dashboard."""
    lines = [
        "🎬 LIVE PROCESSING",
        "",
        f"🎞️ {title}",
        "",
        f"📊 Overall: {overall_percent:5.1f}%",
        progress_bar(overall_percent, 24),
        "",
        f"🔄 Current: {phase}",
        f"{progress_bar(phase_percent, 20)} {phase_percent:5.1f}%",
        "",
        f"⏱️ Elapsed: {format_duration(elapsed)}",
        f"⏳ ETA: {format_eta(eta)}",
    ]

    if completed:
        lines.extend(["", "✅ Completed:", completed])

    if details:
        lines.extend(["", "📡 Live details:", details])

    return "\n".join(lines)


async def monitor_ffmpeg_progress(stream, duration, callback):
    """Read FFmpeg -progress output without changing the encode operation."""
    last_seconds = 0.0
    last_speed = None

    while True:
        raw = await stream.readline()
        if not raw:
            break

        line = raw.decode(errors="replace").strip()

        if line.startswith("out_time_ms="):
            try:
                last_seconds = max(0.0, int(line.split("=", 1)[1]) / 1_000_000)
            except (TypeError, ValueError):
                continue

            percent = (
                min(100.0, (last_seconds / duration) * 100.0)
                if duration and duration > 0
                else 0.0
            )
            callback(percent, last_seconds, last_speed)

        elif line.startswith("speed="):
            value = line.split("=", 1)[1]
            last_speed = value if value and value != "N/A" else None

        elif line == "progress=end":
            callback(100.0, duration, last_speed)


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
            if force:
                self.pending_text = None
                self.pending_force = False
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
    """Fast keyframe-aware stream-copy splitter targeting ~2-minute clips."""
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

    # Pick boundaries between 105 and 120 seconds, preferring 120 seconds.
    boundaries = []
    current = 0.0
    while duration - current > 120.0:
        candidates = [k for k in keyframes if current + 105.0 <= k <= current + 120.0]
        if not candidates:
            raise RuntimeError(
                f"No safe keyframe found between {current + 105:.1f}s and {current + 120:.1f}s. "
                "Cannot create a safe <=120 second stream-copy clip."
            )
        boundary = min(candidates, key=lambda k: abs(k - (current + 120.0)))
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
    clip,
    progress_reporter=None,
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

        workflow_started = time.monotonic()
        loop = asyncio.get_running_loop()

        def schedule_publish_report(phase, phase_percent, overall_percent, details):
            if not progress_reporter:
                return
            text = build_live_processing_report(
                title,
                phase,
                phase_percent,
                overall_percent,
                time.monotonic() - workflow_started,
                None,
                details,
                "📋 Clip selected from the completed Telegram queue",
            )
            loop.call_soon_threadsafe(
                progress_reporter.schedule,
                text,
            )

        if progress_reporter:
            await progress_reporter.edit(
                build_live_processing_report(
                    title,
                    f"INSTAGRAM QUEUE — Part {clip_index}/{queue.get('total_clips', 1)}",
                    0.0,
                    0.0,
                    0.0,
                    None,
                    "📦 Loading the next Telegram clip...",
                    "📋 Clip selected from the completed Telegram queue",
                ),
                force=True,
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
                download_started = time.monotonic()

                def publish_download_progress(current, total):
                    if not progress_reporter or not total:
                        return
                    percent = (current / total) * 100.0
                    elapsed = max(0.01, time.monotonic() - download_started)
                    speed = current / elapsed
                    remaining = max(0, total - current)
                    eta = remaining / speed if speed > 0 else None
                    schedule_publish_report(
                        f"DOWNLOAD TELEGRAM CLIP — Part {clip_index}/{queue.get('total_clips', 1)}",
                        percent,
                        percent * 0.25,
                        (
                            f"📦 {current / 1024 / 1024:.1f} / {total / 1024 / 1024:.1f} MB\n"
                            f"⚡ Speed: {format_rate(speed)}\n"
                            f"⏳ Remaining: {format_duration(eta) if eta is not None else '--'}"
                        ),
                    )

                downloaded = await fast_download_telegram_media(
                    message,
                    local_path,
                    progress_callback=publish_download_progress,
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
            queue.get("total_clips", 1),
            schedule_publish_report,
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

    if bot_settings.get("publishing_paused", False):
        print("⏸️ Instagram publishing is paused.")
        return

    if not window_allows_now():
        print(
            "🕐 Instagram publishing is outside the configured window. "
            f"Window: {format_clock_minutes(bot_settings.get('window_start_minutes', 360))} "
            f"– {format_clock_minutes(bot_settings.get('window_end_minutes', 1260))} IST."
        )
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
                await send_admin_notification(
                    "queue_complete",
                    (
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

            publish_progress_message = None
            if admin_chat_id:
                try:
                    publish_progress_message = await bot_application.bot.send_message(
                        chat_id=admin_chat_id,
                        text=(
                            "🎬 LIVE INSTAGRAM PUBLISHING\n\n"
                            f"🎞️ {title}\n"
                            f"📦 Part {next_index}/{total}\n\n"
                            "🔄 Starting..."
                        ),
                    )
                except Exception as progress_message_error:
                    print(
                        "⚠️ Could not create live Instagram progress message: "
                        f"{type(progress_message_error).__name__}: {str(progress_message_error)}"
                    )

            publish_progress_reporter = (
                TelegramProgressReporter(
                    bot_application.bot,
                    admin_chat_id,
                    publish_progress_message.message_id,
                    min_interval=3.0,
                )
                if publish_progress_message and admin_chat_id
                else None
            )

            try:
                media_id = await publish_one_queue_clip(
                    manifest_message,
                    queue,
                    clip,
                    progress_reporter=publish_progress_reporter,
                )

                if publish_progress_reporter:
                    await publish_progress_reporter.edit(
                        "✅ INSTAGRAM REEL PUBLISHED\n\n"
                        f"🎬 {title}\n"
                        f"📦 Part {next_index}/{total}\n\n"
                        "📊 Overall: 100.0%\n"
                        f"{progress_bar(100, 24)}\n\n"
                        f"🆔 Instagram Media ID: {media_id}\n"
                        + (
                            "🗑️ Telegram clip deleted after successful publishing."
                            if clip.get("deleted_from_telegram")
                            else "⚠️ Instagram published, but Telegram cleanup failed."
                        ),
                        force=True,
                    )

                # Advance only after Instagram has confirmed publication.
                queue["next_clip_index"] = next_index + 1
                queue["last_published_at"] = datetime.now(timezone.utc).isoformat()
                queue["retry_after"] = None

                if queue["next_clip_index"] > total:
                    queue["status"] = "COMPLETED"

                await save_queue_manifest(manifest_message, queue)

                await send_admin_notification(
                    "published",
                    (
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

                if publish_progress_reporter:
                    try:
                        await publish_progress_reporter.edit(
                            "❌ INSTAGRAM PUBLISH FAILED\n\n"
                            f"🎬 {title}\n"
                            f"📦 Part {next_index}/{total}\n\n"
                            "📊 Progress stopped.\n\n"
                            f"❌ {type(e).__name__}: {error_text}\n\n"
                            "⚠️ Telegram clip was kept for retry.",
                            force=True,
                        )
                    except Exception:
                        pass

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

                await send_admin_notification(
                    "publish_failed",
                    (
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
            await send_admin_notification(
                "published",
                (
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
    """Send an upload prompt to the private storage channel on the configured schedule."""
    if not bot_settings.get("notifications", {}).get("upload_reminder", True):
        return

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
            min_interval=3.0,
        )

        print("Downloading original...")

        workflow_started = time.monotonic()
        download_started = workflow_started

        def download_progress(current, total):
            if not total:
                return
            percent = (current / total) * 100.0
            elapsed = max(0.01, time.monotonic() - download_started)
            speed = current / elapsed
            remaining_bytes = max(0, total - current)
            eta = remaining_bytes / speed if speed > 0 else None
            progress_reporter.schedule(
                build_live_processing_report(
                    title,
                    "DOWNLOAD ORIGINAL",
                    percent,
                    percent * 0.15,
                    time.monotonic() - workflow_started,
                    eta,
                    (
                        f"📦 {current / 1024 / 1024:.1f} / {total / 1024 / 1024:.1f} MB\n"
                        f"⚡ Speed: {format_rate(speed)}\n"
                        f"⏳ Remaining: {format_duration(eta) if eta is not None else '--'}"
                    ),
                    "⏳ Downloading source video",
                )
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
            build_live_processing_report(
                title,
                "PREPARING SPLITTER",
                0.0,
                15.0,
                time.monotonic() - workflow_started,
                None,
                (
                    "⚡ Split: keyframe-aware stream copy (-c copy)\n"
                    "🎨 Format: 1080×1920 portrait with black padding\n"
                    "📤 Upload: 512 KB Telegram chunks\n"
                    "🚫 Instagram publishing: blocked until every clip is ready"
                ),
                "✅ Source download complete",
            ),
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
        expected_parts = 0
        split_duration = 0.0

        async def upload_ready_clip(clip_path):
            nonlocal uploaded_count
            index = uploaded_count + 1
            filename = f"{safe_filename(title)} Part {index}.mp4"
            final_path = os.path.join(clips_directory, filename)
            if os.path.abspath(clip_path) != os.path.abspath(final_path):
                os.replace(clip_path, final_path)

            # The splitter above stays stream-copy/fast. Only after a complete
            # split clip exists do we prepare it for the 9:16 Instagram canvas.
            portrait_path = os.path.join(
                clips_directory,
                f".portrait_part_{index:03d}.mp4",
            )
            total_parts = max(1, expected_parts)
            per_clip_span = 70.0 / total_parts
            clip_overall_start = 25.0 + (index - 1) * per_clip_span
            format_span = per_clip_span * 0.50
            upload_span = per_clip_span * 0.50

            await format_clip_for_reels(
                final_path,
                portrait_path,
                progress_reporter=progress_reporter,
                title=title,
                part_index=index,
                total_parts=total_parts,
                overall_start=clip_overall_start,
                overall_span=format_span,
                workflow_started=workflow_started,
                completed=(
                    "✅ Source download complete\n"
                    f"{'🔄 Splitter running' if not splitter_done else '✅ Split completed'}\n"
                    f"📦 Telegram clips uploaded: {uploaded_count}/{total_parts}"
                ),
            )
            os.replace(portrait_path, final_path)

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
                eta = remaining_bytes / speed if speed > 0 else None
                overall = clip_overall_start + format_span + (upload_span * percent / 100.0)
                progress_reporter.schedule(
                    build_live_processing_report(
                        title,
                        f"TELEGRAM UPLOAD — Part {index}/{total_parts}",
                        percent,
                        overall,
                        time.monotonic() - workflow_started,
                        eta,
                        (
                            f"📦 Part {index}/{total_parts}\n"
                            f"💾 {current / 1024 / 1024:.1f} / {total_bytes / 1024 / 1024:.1f} MB\n"
                            f"⚡ Speed: {format_rate(speed)}\n"
                            f"⏳ Remaining: {format_duration(eta) if eta is not None else '--'}\n"
                            f"📤 Uploaded clips: {uploaded_count}/{total_parts}"
                        ),
                        (
                            "✅ Source download complete\n"
                            f"{'🔄 Splitter running' if not splitter_done else '✅ Split completed'}\n"
                            f"📦 Previous clips uploaded: {uploaded_count}/{total_parts}"
                        ),
                    )
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
            # no later than 120 seconds. This preserves the fast -c copy path.
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
            while duration - current > 120.0:
                candidates = [
                    k for k in keyframes
                    if current + 105.0 <= k <= current + 120.0
                ]
                if not candidates:
                    raise RuntimeError(
                        f"No safe keyframe between {current + 105:.1f}s and {current + 120:.1f}s. "
                        "Cannot create a stream-copy clip that stays within 120 seconds."
                    )
                boundary = min(candidates, key=lambda k: abs(k - (current + 120.0)))
                boundaries.append(boundary)
                current = boundary

            nonlocal expected_parts, split_duration
            expected_parts = len(boundaries) + 1
            split_duration = duration

            command = [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                "-i", original_path,
                "-map", "0:v:0", "-map", "0:a:0?",
                "-c", "copy",
                "-f", "segment",
                "-segment_times", ",".join(f"{x:.3f}" for x in boundaries),
                "-reset_timestamps", "1",
                "-segment_format", "mp4",
                "-progress", "pipe:1",
                os.path.join(clips_directory, "part_%03d.mp4"),
            ]
            print("Running FAST stream-copy FFmpeg:")
            print(" ".join(command))
            proc = await asyncio.create_subprocess_exec(
                *command,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )

            def split_progress(percent, processed_seconds, ffmpeg_speed):
                elapsed = max(0.01, time.monotonic() - workflow_started)
                overall = 15.0 + (10.0 * percent / 100.0)
                details = (
                    f"🎞️ Source duration: {format_duration(duration)}\n"
                    f"⏱️ Segmented: {format_duration(processed_seconds)} / {format_duration(duration)}\n"
                    f"✂️ Expected parts: {expected_parts}\n"
                    f"⚡ FFmpeg speed: {ffmpeg_speed or 'working'}\n"
                    f"📤 Uploaded clips: {uploaded_count}/{expected_parts}"
                )
                progress_reporter.schedule(
                    build_live_processing_report(
                        title,
                        "FAST SPLIT — STREAM COPY",
                        percent,
                        overall,
                        elapsed,
                        None,
                        details,
                        (
                            "✅ Source download complete\n"
                            "🔄 FFmpeg is splitting without re-encoding"
                        ),
                    )
                )

            split_progress_task = asyncio.create_task(
                monitor_ffmpeg_progress(proc.stdout, duration, split_progress)
            )
            stderr_task = asyncio.create_task(proc.stderr.read())
            return proc, stderr_task, split_progress_task, duration, boundaries

        process, stderr_task, split_progress_task, source_duration, boundaries = await run_stream_splitter()
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
        await split_progress_task
        splitter_done = True
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

        await progress_reporter.edit(
            build_live_processing_report(
                title,
                "PROCESSING COMPLETE — FINALIZING",
                100.0,
                95.0,
                time.monotonic() - workflow_started,
                None,
                (
                    f"✂️ Parts created: {len(uploaded_messages)}\n"
                    "📤 All parts uploaded to Telegram\n"
                    "📋 Instagram publishing is still blocked until this workflow finishes finalization"
                ),
                (
                    "✅ Source download complete\n"
                    "✅ Stream-copy split complete\n"
                    "✅ Portrait formatting complete\n"
                    "✅ Telegram upload complete"
                ),
            ),
            force=True,
        )

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

        await progress_reporter.edit(
            build_live_processing_report(
                title,
                "DELETING ORIGINAL VIDEO",
                100.0,
                97.0,
                time.monotonic() - workflow_started,
                None,
                (
                    f"🗑️ Removing original Telegram message {video_message_id}...\n"
                    "🔒 Generated clips and queue are already safe in Telegram."
                ),
                (
                    "✅ Source download complete\n"
                    "✅ Stream-copy split complete\n"
                    "✅ Portrait formatting complete\n"
                    "✅ Telegram upload complete\n"
                    "✅ Queue manifest saved"
                ),
            ),
            force=True,
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
            f"📊 Overall: 100.0%\n"
            f"{progress_bar(100, 24)}\n\n"
            f"✂️ Parts created: {len(uploaded_messages)}\n"
            "📤 All parts uploaded to Telegram\n"
            "🎨 All clips formatted to 1080×1920\n"
            "🗑️ Original video deleted\n\n"
            "📋 Instagram queue created.\n"
            "⏳ Waiting for automatic Instagram publishing.",
            force=True,
        )

        await send_admin_notification(
            "processing_complete",
            (
                "✅ VIDEO PROCESSING COMPLETE!\n\n"
                f"🎬 {title}\n"
                f"✂️ Parts created: {len(uploaded_messages)}\n"
                "📋 Instagram queue created and ready."
            )
        )

    except (Exception, asyncio.CancelledError) as e:

        was_cancelled = isinstance(e, asyncio.CancelledError)

        print(
            "🛑 VIDEO PROCESSING CANCELLED"
            if was_cancelled
            else "❌ VIDEO PROCESSING FAILED"
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
            await send_admin_notification(
                "processing_complete" if was_cancelled else "processing_failed",
                (
                    (
                        "🛑 VIDEO PROCESSING CANCELLED\n\n"
                        f"🎬 {title}\n\n"
                        "⚠️ The original video was NOT deleted.\n"
                        f"Your video is still safe in {STORAGE_CHANNEL_NAME}.\n\n"
                    )
                    if was_cancelled
                    else
                    (
                        "❌ VIDEO PROCESSING FAILED\n\n"
                        f"🎬 {title}\n\n"
                        f"Error: {type(e).__name__}\n"
                        f"{str(e)}\n\n"
                        "⚠️ The original video was NOT deleted.\n"
                        f"Your video is still safe in {STORAGE_CHANNEL_NAME}.\n\n"
                    )
                )
                + (
                    "Generated partial clips from this cancelled processing "
                    "attempt were cleaned up."
                    if was_cancelled and not processing_complete
                    else
                    "Generated partial clips from this failed processing "
                    "attempt were cleaned up."
                    if not was_cancelled and not processing_complete
                    else
                    "The completed Instagram queue was preserved."
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
    global current_processing_task

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

    pending_video_message_id = video_message_id

    print("🎬 TITLE RECEIVED")
    print(f"Title: {title}")
    print(f"Video message ID: {video_message_id}")

    await update.message.reply_text(
        "✅ Title received!\n\n"
        f"🎬 {title}\n\n"
        "🚀 Starting automatic processing..."
    )

    current_processing_task = asyncio.current_task()

    try:
        await process_original_video(
            video_message_id,
            title,
            chat_id
        )
    finally:
        if current_processing_task is asyncio.current_task():
            current_processing_task = None



# ============================================================
# TELEGRAM CONTROL COMMANDS
# ============================================================

async def command_is_admin(update):
    if not update or not update.effective_chat:
        return False
    return await load_admin_chat_id() == update.effective_chat.id


def format_clock_minutes(total_minutes):
    total_minutes = int(total_minutes) % 1440
    hour, minute = divmod(total_minutes, 60)
    suffix = "AM" if hour < 12 else "PM"
    display_hour = hour % 12 or 12
    return f"{display_hour:02d}:{minute:02d} {suffix}"


def format_duration_human(seconds):
    seconds = max(0, int(seconds))
    if seconds % 3600 == 0:
        return f"{seconds // 3600}h"
    if seconds % 60 == 0:
        minutes = seconds // 60
        if minutes >= 60:
            h, m = divmod(minutes, 60)
            return f"{h}h {m}m" if m else f"{h}h"
        return f"{minutes}m"
    m, s = divmod(seconds, 60)
    return f"{m}m {s}s"


def parse_clock(value):
    match = re.fullmatch(r"([01]?\d|2[0-3]):([0-5]\d)", value.strip())
    if not match:
        raise ValueError("Use HH:MM, for example 06:00 or 21:00.")
    return int(match.group(1)) * 60 + int(match.group(2))


def parse_duration(value, minimum_seconds=60):
    value = value.strip().lower().replace(" ", "")
    if value.isdigit():
        seconds = int(value)
    else:
        matches = re.findall(r"(\d+)([smhd])", value)
        if not matches or "".join(n + u for n, u in matches) != value:
            raise ValueError("Use 30m, 1h, 90m, or 1h30m.")
        mult = {"s": 1, "m": 60, "h": 3600, "d": 86400}
        seconds = sum(int(n) * mult[u] for n, u in matches)
    if seconds < minimum_seconds:
        raise ValueError(
            f"Minimum is {format_duration_human(minimum_seconds)}."
        )
    return seconds


def window_allows_now(now=None):
    if not bot_settings.get("window_enabled", True):
        return True
    now = now or datetime.now(INSTAGRAM_TIMEZONE)
    current = now.hour * 60 + now.minute
    start = int(bot_settings.get("window_start_minutes", 360))
    end = int(bot_settings.get("window_end_minutes", 1260))
    if start == end:
        return True
    if start < end:
        return start <= current <= end
    return current >= start or current <= end


def next_window_start(now=None):
    now = now or datetime.now(INSTAGRAM_TIMEZONE)
    if not bot_settings.get("window_enabled", True):
        return now

    start = int(bot_settings.get("window_start_minutes", 360))
    end = int(bot_settings.get("window_end_minutes", 1260))
    current = now.hour * 60 + now.minute

    if start == end:
        return now

    if start < end:
        if start <= current <= end:
            return now
        date_value = now.date() if current < start else now.date() + timedelta(days=1)
    else:
        if current >= start or current <= end:
            return now
        date_value = now.date() + timedelta(days=1)

    return datetime(
        date_value.year, date_value.month, date_value.day,
        start // 60, start % 60,
        tzinfo=INSTAGRAM_TIMEZONE
    )


def next_publish_time_from_state(last_publish=None):
    if bot_settings.get("publishing_paused"):
        return None

    now = datetime.now(INSTAGRAM_TIMEZONE)
    candidate = now

    if last_publish is not None:
        if last_publish.tzinfo is None:
            last_publish = last_publish.replace(tzinfo=timezone.utc)
        candidate = (
            last_publish + timedelta(seconds=INSTAGRAM_POST_INTERVAL_SECONDS)
        ).astimezone(INSTAGRAM_TIMEZONE)

    return max(candidate, next_window_start(candidate))


async def send_admin_notification(kind, text):
    if not admin_chat_id:
        return
    if not bot_settings.get("notifications", {}).get(kind, True):
        return
    try:
        await bot_application.bot.send_message(
            chat_id=admin_chat_id,
            text=text
        )
    except Exception as e:
        print(
            f"⚠️ Could not send {kind} notification: "
            f"{type(e).__name__}: {str(e)}"
        )


def queue_summary(queue):
    total = int(queue.get("total_clips", 0))
    skipped = len(queue.get("skipped_parts", []))

    if queue.get("queue_version") == 2 and "clip_message_ids" in queue:
        processed = max(
            0,
            min(total, int(queue.get("next_clip_index", 1)) - 1)
        )
        published = max(0, processed - skipped)
    else:
        clips = queue.get("clips", [])
        published = sum(
            1 for clip in clips
            if clip.get("instagram_status") == "PUBLISHED"
        )
        skipped = sum(
            1 for clip in clips
            if clip.get("instagram_status") == "SKIPPED"
        )

    waiting = max(0, total - published - skipped)
    return published, waiting, total


async def help_command(update, context):
    if not await command_is_admin(update):
        return
    await update.message.reply_text(
        "🤖 CARTOON VIBES TELUGU BOT\n\n"
        "📊 INFO\n"
        "/status — complete status\n"
        "/queue — all pending queues\n"
        "/next — next Reel\n"
        "/history — completed videos\n"
        "/jobs — active jobs\n"
        "/storage — Telegram storage\n\n"
        "⚙️ INSTAGRAM\n"
        "/window — publishing window\n"
        "/interval — Reel interval\n"
        "/pause — pause publishing\n"
        "/resume — resume publishing\n"
        "/retry — retry failed Reel\n"
        "/skip — skip next Reel\n"
        "/quota — Meta publishing quota\n"
        "/publish_queue — run queue check now\n\n"
        "🔔 NOTIFICATIONS\n"
        "/reminder — upload reminder\n"
        "/notifications — notification controls\n\n"
        "🛠️ SYSTEM\n"
        "/settings — all settings\n"
        "/test_telegram — Telegram test\n"
        "/test_instagram — Instagram test\n"
        "/test_public_url — public URL test\n"
        "/cancel — cancel current processing\n"
        "/clear_completed — clean completed manifests\n\n"
        "Examples:\n"
        "/window 06:00 21:00\n"
        "/window off\n"
        "/interval 1h\n"
        "/reminder 2h\n"
        "/notifications published off\n"
        "/skip confirm\n"
        "/clear_completed confirm"
    )


async def status_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        await load_bot_config()
        processing = await load_processing_state()
        manifests = await find_queue_manifests()

        pending = []
        waiting_clips = 0
        for item in manifests:
            q = item["queue"]
            if q.get("status") == "COMPLETED":
                continue
            pub, wait, total = queue_summary(q)
            waiting_clips += wait
            pending.append((q, pub, wait, total))

        telegram_ok = bool(telethon_client and telethon_client.is_connected())
        instagram_ok = bool(INSTAGRAM_ACCESS_TOKEN and INSTAGRAM_USER_ID)
        public_ok = bool(PUBLIC_BASE_URL)

        last_publish = await get_last_successful_instagram_publish_time(manifests)
        next_time = next_publish_time_from_state(last_publish)

        if bot_settings.get("publishing_paused"):
            publish_state = "⏸️ PAUSED"
            next_text = "Paused"
        elif not window_allows_now():
            publish_state = "🕐 OUTSIDE WINDOW"
            next_text = (
                next_time.strftime("%I:%M %p IST")
                if next_time else "Not scheduled"
            )
        else:
            publish_state = "🟢 ACTIVE"
            next_text = (
                next_time.strftime("%I:%M %p IST")
                if next_time else "Ready"
            )

        lines = [
            "📊 BOT STATUS",
            "",
            "🟢 Bot: ONLINE",
            f"{'🟢' if telegram_ok else '🔴'} Telegram/Telethon: "
            f"{'CONNECTED' if telegram_ok else 'NOT CONNECTED'}",
            f"{'🟢' if instagram_ok else '🔴'} Instagram: "
            f"{'CONFIGURED' if instagram_ok else 'MISSING'}",
            f"{'🟢' if public_ok else '🔴'} Public URL: "
            f"{'CONFIGURED' if public_ok else 'MISSING'}",
            "",
            "🎬 PROCESSING",
        ]

        if processing:
            lines += [
                f"Current: {processing.get('title', 'Unknown')}",
                f"Video ID: {processing.get('video_message_id', 'Unknown')}",
            ]
        else:
            lines.append("Current: None")

        lines += [
            "",
            "📋 QUEUE",
            f"Pending videos: {len(pending)}",
            f"Clips waiting: {waiting_clips}",
            "",
            "📤 INSTAGRAM",
            f"Publishing: {publish_state}",
            f"Interval: {format_duration_human(INSTAGRAM_POST_INTERVAL_SECONDS)}",
            "Window: " + (
                f"{format_clock_minutes(bot_settings['window_start_minutes'])} – "
                f"{format_clock_minutes(bot_settings['window_end_minutes'])} IST"
                if bot_settings.get("window_enabled")
                else "24/7"
            ),
            f"Next allowed: {next_text}",
            "",
            "🔔 REMINDER",
            f"Every: {format_duration_human(UPLOAD_REMINDER_INTERVAL_SECONDS)}",
        ]

        if pending:
            q, pub, wait, total = pending[0]
            lines += [
                "",
                "➡️ NEXT QUEUE",
                f"{q.get('title', 'Untitled')}",
                f"Progress: {pub}/{total}",
                f"Next part: {q.get('next_clip_index', pub + 1)}",
            ]

        await update.message.reply_text("\n".join(lines))
    except Exception as e:
        await update.message.reply_text(
            f"❌ STATUS CHECK FAILED\n\n{type(e).__name__}: {str(e)}"
        )


async def queue_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        manifests = await find_queue_manifests()
        active = [
            item for item in manifests
            if item["queue"].get("status") != "COMPLETED"
        ]
        if not active:
            await update.message.reply_text(
                "📋 QUEUE IS EMPTY\n\nNo pending Instagram queues."
            )
            return

        lines = ["📋 INSTAGRAM QUEUES", ""]
        for i, item in enumerate(active, 1):
            q = item["queue"]
            pub, wait, total = queue_summary(q)
            lines += [
                f"{i}️⃣ {q.get('title', 'Untitled')}",
                f"   Status: {q.get('status', 'PENDING')}",
                f"   Processing complete: "
                f"{'YES' if q.get('processing_complete') else 'NO'}",
                f"   Published: {pub}/{total}",
                f"   Skipped: {len(q.get('skipped_parts', []))}",
                f"   Waiting: {wait}",
                f"   Next part: {q.get('next_clip_index', pub + 1) if wait else 'None'}",
            ]
            if q.get("retry_after"):
                lines.append(f"   Retry after: {q['retry_after']}")
            lines.append("")

        lines.append(f"Pending queues: {len(active)}")
        reply_text = "\n".join(lines)
        if len(reply_text) > 3500:
            reply_text = reply_text[:3500] + "\n\n…output truncated…"
        await update.message.reply_text(reply_text)
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not read queues.\n\n{type(e).__name__}: {str(e)}"
        )


async def next_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        manifests = await find_queue_manifests()
        target = None
        for item in manifests:
            q = item["queue"]
            if q.get("status") == "COMPLETED" or not q.get("processing_complete"):
                continue
            pub, wait, total = queue_summary(q)
            if wait:
                target = (q, pub, total)
                break

        if target is None:
            await update.message.reply_text(
                "📤 NEXT REEL\n\nNo ready queued Reel."
            )
            return

        q, pub, total = target
        last_publish = await get_last_successful_instagram_publish_time(manifests)
        next_time = next_publish_time_from_state(last_publish)

        if q.get("retry_after"):
            try:
                retry_time = datetime.fromisoformat(
                    q["retry_after"].replace("Z", "+00:00")
                ).astimezone(INSTAGRAM_TIMEZONE)
                if retry_time > datetime.now(INSTAGRAM_TIMEZONE):
                    next_time = retry_time
            except Exception:
                pass

        next_text = (
            "Paused"
            if bot_settings.get("publishing_paused")
            else next_time.strftime("%I:%M %p IST") if next_time else "Ready"
        )

        await update.message.reply_text(
            "📤 NEXT INSTAGRAM REEL\n\n"
            f"🎬 {q.get('title', 'Untitled')}\n"
            f"📌 Part: {q.get('next_clip_index', pub + 1)}/{total}\n"
            f"📊 Published: {pub}/{total}\n"
            f"⏱️ Next allowed: {next_text}\n"
            "🕐 Window: " + (
                f"{format_clock_minutes(bot_settings['window_start_minutes'])} – "
                f"{format_clock_minutes(bot_settings['window_end_minutes'])} IST"
                if bot_settings.get("window_enabled") else "24/7"
            )
        )
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not determine next Reel.\n\n{type(e).__name__}: {str(e)}"
        )


async def history_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        manifests = await find_queue_manifests()
        completed = [
            item for item in manifests
            if item["queue"].get("status") == "COMPLETED"
        ]
        completed.sort(
            key=lambda x: x["queue"].get("last_published_at")
            or x["queue"].get("created_at", ""),
            reverse=True
        )

        if not completed:
            await update.message.reply_text(
                "📜 HISTORY\n\nNo completed queues yet."
            )
            return

        lines = ["📜 RECENT HISTORY", ""]
        for i, item in enumerate(completed[:10], 1):
            q = item["queue"]
            pub, _, total = queue_summary(q)
            skipped = len(q.get("skipped_parts", []))
            lines += [
                f"{i}. {q.get('title', 'Untitled')}",
                f"   Published: {pub}/{total}",
                f"   Skipped: {skipped}",
                f"   Last activity: {q.get('last_published_at', 'Unknown')}",
                "",
            ]
        await update.message.reply_text("\n".join(lines))
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not read history.\n\n{type(e).__name__}: {str(e)}"
        )


async def window_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        args = context.args
        if not args:
            await update.message.reply_text(
                "🕐 PUBLISHING WINDOW\n\n" + (
                    f"Start: {format_clock_minutes(bot_settings['window_start_minutes'])}\n"
                    f"End: {format_clock_minutes(bot_settings['window_end_minutes'])}\n"
                    "Timezone: Asia/Kolkata (IST)\n"
                    "Status: ENABLED"
                    if bot_settings.get("window_enabled")
                    else "Status: DISABLED (24/7)"
                )
            )
            return

        if len(args) == 1 and args[0].lower() in {"off", "disable", "disabled"}:
            bot_settings["window_enabled"] = False
            await save_bot_config()
            await update.message.reply_text(
                "✅ Publishing window disabled.\n\nInstagram publishing is now allowed 24/7."
            )
            return

        if len(args) != 2:
            raise ValueError("Use /window 06:00 21:00 or /window off.")

        start_minutes = parse_clock(args[0])
        end_minutes = parse_clock(args[1])
        if start_minutes == end_minutes:
            raise ValueError("Start and end cannot be identical. Use /window off for 24/7.")

        bot_settings["window_enabled"] = True
        bot_settings["window_start_minutes"] = start_minutes
        bot_settings["window_end_minutes"] = end_minutes
        _apply_bot_settings(bot_settings)
        await save_bot_config()

        await update.message.reply_text(
            "✅ PUBLISHING WINDOW UPDATED\n\n"
            f"Start: {format_clock_minutes(start_minutes)}\n"
            f"End: {format_clock_minutes(end_minutes)}\n"
            "Timezone: Asia/Kolkata (IST)"
        )
    except Exception as e:
        await update.message.reply_text(f"❌ Window not changed.\n\n{str(e)}")


async def interval_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        if not context.args:
            await update.message.reply_text(
                "⏱️ INSTAGRAM POST INTERVAL\n\n"
                f"Current: {format_duration_human(INSTAGRAM_POST_INTERVAL_SECONDS)}\n"
                f"Seconds: {INSTAGRAM_POST_INTERVAL_SECONDS}"
            )
            return

        seconds = parse_duration(context.args[0], 60)
        bot_settings["interval_seconds"] = seconds
        _apply_bot_settings(bot_settings)
        await save_bot_config()

        await update.message.reply_text(
            "✅ INTERVAL UPDATED\n\n"
            f"Interval: {format_duration_human(seconds)}"
        )
    except Exception as e:
        await update.message.reply_text(f"❌ Interval not changed.\n\n{str(e)}")


async def quota_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        if not INSTAGRAM_ACCESS_TOKEN or not INSTAGRAM_USER_ID:
            await update.message.reply_text("❌ Instagram credentials are missing.")
            return

        await update.message.reply_text("🔎 Checking Instagram publishing quota...")
        status_code, data = instagram_api_get(
            f"{INSTAGRAM_USER_ID}/content_publishing_limit"
        )
        pretty = json.dumps(data, ensure_ascii=False, indent=2)
        if len(pretty) > 3000:
            pretty = pretty[:3000] + "\n..."

        await update.message.reply_text(
            "📊 INSTAGRAM PUBLISHING QUOTA\n\n"
            f"HTTP status: {status_code}\n\n{pretty}"
        )
    except Exception as e:
        await update.message.reply_text(
            f"❌ COULD NOT READ INSTAGRAM QUOTA\n\n{type(e).__name__}: {str(e)}"
        )


async def pause_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        bot_settings["publishing_paused"] = True
        await save_bot_config()
        await update.message.reply_text(
            "⏸️ INSTAGRAM PUBLISHING PAUSED\n\n"
            "Video processing and Telegram clip uploads continue normally.\n"
            "Use /resume to continue."
        )
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not pause publishing.\n\n{type(e).__name__}: {str(e)}"
        )


async def resume_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        bot_settings["publishing_paused"] = False
        await save_bot_config()
        await update.message.reply_text(
            "▶️ INSTAGRAM PUBLISHING RESUMED\n\n"
            "The next eligible Reel will be published automatically."
        )
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not resume publishing.\n\n{type(e).__name__}: {str(e)}"
        )


async def retry_command(update, context):
    if not await command_is_admin(update):
        return
    if queue_publish_lock.locked():
        await update.message.reply_text(
            "⏳ A Reel is currently being published. Please wait."
        )
        return

    try:
        manifests = await find_queue_manifests()
        target = None
        for item in manifests:
            q = item["queue"]
            if q.get("status") == "COMPLETED":
                continue
            if q.get("retry_after"):
                target = item
                break
            if any(c.get("instagram_status") == "FAILED" for c in q.get("clips", [])):
                target = item
                break

        if not target:
            await update.message.reply_text("ℹ️ No failed Instagram queue found.")
            return

        q = target["queue"]
        q["retry_after"] = None
        if q.get("queue_version") != 2:
            for clip in q.get("clips", []):
                if clip.get("instagram_status") == "FAILED":
                    clip["instagram_status"] = "NOT_POSTED"
                    clip["status"] = "PENDING"
                    break

        await save_queue_manifest(target["message"], q)
        await update.message.reply_text(
            f"🔄 RETRYING\n\n🎬 {q.get('title', 'Untitled')}\n"
            "Normal interval/window rules still apply."
        )
        await process_pending_queues()
    except Exception as e:
        await update.message.reply_text(
            f"❌ Retry failed.\n\n{type(e).__name__}: {str(e)}"
        )


async def skip_command(update, context):
    if not await command_is_admin(update):
        return
    if not context.args or context.args[0].lower() != "confirm":
        await update.message.reply_text(
            "⚠️ This permanently skips the next ready queued clip and "
            "deletes that Telegram clip.\n\nUse /skip confirm to continue."
        )
        return
    if queue_publish_lock.locked():
        await update.message.reply_text(
            "⏳ A Reel is currently being published. Please wait."
        )
        return

    try:
        manifests = await find_queue_manifests()
        storage_channel = await find_storage_channel()

        for item in manifests:
            q = item["queue"]
            if q.get("status") == "COMPLETED" or not q.get("processing_complete"):
                continue

            if q.get("queue_version") == 2 and "clip_message_ids" in q:
                total = int(q.get("total_clips", 0))
                next_index = int(q.get("next_clip_index", 1))
                ids = q.get("clip_message_ids", [])
                if next_index > total or next_index > len(ids):
                    continue

                # Persist the skip decision before deleting the clip.
                q.setdefault("skipped_parts", []).append(next_index)
                q["next_clip_index"] = next_index + 1
                if q["next_clip_index"] > total:
                    q["status"] = "COMPLETED"
                await save_queue_manifest(item["message"], q)

                try:
                    await telethon_client.delete_messages(
                        storage_channel, ids[next_index - 1]
                    )
                except Exception as delete_error:
                    await update.message.reply_text(
                        "⚠️ Queue advanced safely, but Telegram clip deletion failed.\n\n"
                        f"Part: {next_index}/{total}\n"
                        f"Error: {type(delete_error).__name__}: {delete_error}"
                    )
                    return

                await update.message.reply_text(
                    "⏭️ CLIP SKIPPED\n\n"
                    f"🎬 {q.get('title', 'Untitled')}\n"
                    f"Part: {next_index}/{total}\n"
                    "🗑️ Telegram clip deleted."
                )
                return

            for clip in q.get("clips", []):
                if clip.get("instagram_status") in {"PUBLISHED", "SKIPPED"}:
                    continue
                clip_index = clip.get("index")
                clip["instagram_status"] = "SKIPPED"
                clip["status"] = "SKIPPED"
                q.setdefault("skipped_parts", []).append(clip_index)
                q["next_clip_index"] = int(clip_index) + 1
                await save_queue_manifest(item["message"], q)
                try:
                    await telethon_client.delete_messages(
                        storage_channel, clip.get("telegram_message_id")
                    )
                except Exception as delete_error:
                    await update.message.reply_text(
                        f"⚠️ Queue advanced, but Telegram deletion failed: {delete_error}"
                    )
                    return
                await update.message.reply_text(
                    f"⏭️ Skipped Part {clip_index} of {q.get('title', 'Untitled')}."
                )
                return

        await update.message.reply_text("ℹ️ No ready queued clip is available to skip.")
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not skip the queued clip.\n\n{type(e).__name__}: {str(e)}"
        )


async def reminder_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        if not context.args:
            await update.message.reply_text(
                "🔔 UPLOAD REMINDER\n\n"
                f"Interval: {format_duration_human(UPLOAD_REMINDER_INTERVAL_SECONDS)}\n"
                f"Enabled: {'YES' if bot_settings['notifications'].get('upload_reminder', True) else 'NO'}\n"
                "Minimum interval: 1 hour"
            )
            return

        if len(context.args) == 1 and context.args[0].lower() == "off":
            bot_settings["notifications"]["upload_reminder"] = False
            await save_bot_config()
            await update.message.reply_text(
                "🔕 Upload reminder disabled."
            )
            return

        seconds = parse_duration(context.args[0], 3600)
        bot_settings["reminder_seconds"] = seconds
        bot_settings["notifications"]["upload_reminder"] = True
        _apply_bot_settings(bot_settings)
        await save_bot_config()

        await update.message.reply_text(
            f"✅ Upload reminder set to every {format_duration_human(seconds)}."
        )
    except Exception as e:
        await update.message.reply_text(f"❌ Reminder not changed.\n\n{str(e)}")


async def settings_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        n = bot_settings.get("notifications", {})
        await update.message.reply_text(
            "⚙️ BOT SETTINGS\n\n"
            "📤 INSTAGRAM\n"
            f"Interval: {format_duration_human(INSTAGRAM_POST_INTERVAL_SECONDS)}\n"
            f"Publishing: {'PAUSED' if bot_settings.get('publishing_paused') else 'ACTIVE'}\n"
            "Window: " + (
                f"{format_clock_minutes(bot_settings['window_start_minutes'])} – "
                f"{format_clock_minutes(bot_settings['window_end_minutes'])} IST"
                if bot_settings.get("window_enabled") else "24/7"
            ) + "\n\n"
            "🔔 REMINDER\n"
            f"Interval: {format_duration_human(UPLOAD_REMINDER_INTERVAL_SECONDS)}\n"
            f"Enabled: {'YES' if n.get('upload_reminder', True) else 'NO'}\n\n"
            "🔔 NOTIFICATIONS\n"
            f"Processing complete: {'ON' if n.get('processing_complete', True) else 'OFF'}\n"
            f"Processing failed: {'ON' if n.get('processing_failed', True) else 'OFF'}\n"
            f"Reel published: {'ON' if n.get('published', True) else 'OFF'}\n"
            f"Publish failed: {'ON' if n.get('publish_failed', True) else 'OFF'}\n"
            f"Queue complete: {'ON' if n.get('queue_complete', True) else 'OFF'}\n\n"
            "🌏 Timezone: Asia/Kolkata (IST)\n"
            "✂️ Splitter: ~2-minute keyframe-aware stream copy\n"
            "📦 Telegram transfer: 512 KB chunks"
        )
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not read settings.\n\n{type(e).__name__}: {str(e)}"
        )


async def storage_command(update, context):
    if not await command_is_admin(update):
        return
    try:
        storage_channel = await find_storage_channel()
        if storage_channel is None:
            raise RuntimeError(f'Could not find "{STORAGE_CHANNEL_NAME}".')

        messages = await telethon_client.get_messages(storage_channel, limit=200)
        counts = {
            "videos": 0, "clips": 0, "queues": 0, "processing": 0,
            "titles": 0, "config": 0, "reminders": 0
        }

        for message in messages:
            text = message.message or ""
            if message.video:
                counts["videos"] += 1
                if text.startswith(CLIP_MARKER):
                    counts["clips"] += 1
            if text.startswith(QUEUE_MARKER):
                counts["queues"] += 1
            elif text.startswith(PROCESSING_MARKER):
                counts["processing"] += 1
            elif text.startswith(TITLE_REQUEST_MARKER):
                counts["titles"] += 1
            elif text.startswith(CONFIG_MARKER):
                counts["config"] += 1
            elif text.startswith(UPLOAD_REMINDER_MARKER):
                counts["reminders"] += 1

        await update.message.reply_text(
            "📦 TELEGRAM STORAGE\n\n"
            f"Channel: {STORAGE_CHANNEL_NAME}\n"
            f"Video messages: {counts['videos']}\n"
            f"Generated clips: {counts['clips']}\n"
            f"Queue manifests: {counts['queues']}\n"
            f"Processing state: {counts['processing']}\n"
            f"Title requests: {counts['titles']}\n"
            f"Reminder messages: {counts['reminders']}\n"
            f"Config messages: {counts['config']}\n\n"
            "ℹ️ Latest 200 channel messages are counted."
        )
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not inspect storage.\n\n{type(e).__name__}: {str(e)}"
        )


async def clear_completed_command(update, context):
    if not await command_is_admin(update):
        return

    manifests = await find_queue_manifests()
    completed = [
        item for item in manifests
        if item["queue"].get("status") == "COMPLETED"
    ]

    if not context.args or context.args[0].lower() != "confirm":
        await update.message.reply_text(
            "🧹 CLEAR COMPLETED QUEUES\n\n"
            f"Completed manifests: {len(completed)}\n\n"
            "Only completed queue-manifest messages will be deleted.\n"
            "Use /clear_completed confirm to continue."
        )
        return

    storage_channel = await find_storage_channel()
    deleted = 0
    for item in completed:
        try:
            await telethon_client.delete_messages(
                storage_channel, item["message"].id
            )
            deleted += 1
        except Exception as e:
            print(
                f"⚠️ Could not delete completed manifest "
                f"{item['message'].id}: {type(e).__name__}: {str(e)}"
            )

    await update.message.reply_text(
        "🧹 COMPLETED QUEUE CLEANUP FINISHED\n\n"
        f"Deleted: {deleted}\n"
        f"Failed: {len(completed) - deleted}"
    )


async def cancel_command(update, context):
    global current_processing_task

    if not await command_is_admin(update):
        return

    task = current_processing_task
    if task is None or task.done():
        await update.message.reply_text(
            "ℹ️ No video is currently being processed."
        )
        return

    task.cancel()
    await update.message.reply_text(
        "🛑 CANCELLATION REQUESTED\n\n"
        "The current processing task is being stopped.\n"
        "The original video will be kept in Telegram."
    )


async def jobs_command(update, context):
    if not await command_is_admin(update):
        return

    try:
        processing = await load_processing_state()
        manifests = await find_queue_manifests()
        lines = ["🧩 CURRENT JOBS", ""]

        if processing:
            lines += [
                "🟢 ACTIVE PROCESSING",
                f"🎬 {processing.get('title', 'Unknown')}",
                f"Video ID: {processing.get('video_message_id', 'Unknown')}",
                ""
            ]
        else:
            lines += ["🟢 ACTIVE PROCESSING", "None", ""]

        found = False
        for item in manifests:
            q = item["queue"]
            if q.get("status") == "COMPLETED":
                continue
            found = True
            pub, wait, total = queue_summary(q)
            lines += [
                "📋 INSTAGRAM QUEUE",
                f"🎬 {q.get('title', 'Untitled')}",
                f"Progress: {pub}/{total}",
                f"Waiting: {wait}",
                f"Processing complete: {'YES' if q.get('processing_complete') else 'NO'}",
                ""
            ]

        if not found:
            lines.append("📋 INSTAGRAM QUEUES\nNone")

        reply_text = "\n".join(lines)
        if len(reply_text) > 3500:
            reply_text = reply_text[:3500] + "\n\n…output truncated…"
        await update.message.reply_text(reply_text)
    except Exception as e:
        await update.message.reply_text(
            f"❌ Could not read jobs.\n\n{type(e).__name__}: {str(e)}"
        )


async def notifications_command(update, context):
    if not await command_is_admin(update):
        return

    aliases = {
        "processing": "processing_complete",
        "processing_complete": "processing_complete",
        "processing_failed": "processing_failed",
        "published": "published",
        "publish": "published",
        "failed": "publish_failed",
        "publish_failed": "publish_failed",
        "complete": "queue_complete",
        "queue_complete": "queue_complete",
        "reminder": "upload_reminder",
        "upload_reminder": "upload_reminder",
    }

    try:
        if not context.args:
            n = bot_settings["notifications"]
            await update.message.reply_text(
                "🔔 NOTIFICATIONS\n\n"
                f"Processing complete: {'ON' if n.get('processing_complete', True) else 'OFF'}\n"
                f"Processing failed: {'ON' if n.get('processing_failed', True) else 'OFF'}\n"
                f"Reel published: {'ON' if n.get('published', True) else 'OFF'}\n"
                f"Publish failed: {'ON' if n.get('publish_failed', True) else 'OFF'}\n"
                f"Queue complete: {'ON' if n.get('queue_complete', True) else 'OFF'}\n"
                f"Upload reminder: {'ON' if n.get('upload_reminder', True) else 'OFF'}\n\n"
                "Use /notifications NAME on|off or /notifications all on|off."
            )
            return

        if len(context.args) == 2 and context.args[0].lower() == "all":
            value = context.args[1].lower()
            if value not in {"on", "off"}:
                raise ValueError("Use on or off.")
            for key in bot_settings["notifications"]:
                bot_settings["notifications"][key] = value == "on"
        elif len(context.args) == 2:
            key = aliases.get(context.args[0].lower())
            value = context.args[1].lower()
            if key is None:
                raise ValueError(
                    "Use processing, processing_failed, published, failed, complete, or reminder."
                )
            if value not in {"on", "off"}:
                raise ValueError("Use on or off.")
            bot_settings["notifications"][key] = value == "on"
        else:
            raise ValueError("Use /notifications NAME on|off.")

        await save_bot_config()
        await update.message.reply_text("✅ Notification settings updated.")
    except Exception as e:
        await update.message.reply_text(
            f"❌ Notification setting not changed.\n\n{str(e)}"
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
    Load persistent settings, register the Telegram command menu,
    then start the Instagram queue worker.
    """
    try:
        await load_bot_config()
    except Exception as e:
        print(
            "⚠️ Could not load persistent bot settings at startup: "
            f"{type(e).__name__}: {str(e)}"
        )
        _apply_bot_settings(bot_settings)

    try:
        await application.bot.set_my_commands([
            BotCommand("start", "Connect this Telegram account"),
            BotCommand("help", "Show all commands"),
            BotCommand("status", "Show complete bot status"),
            BotCommand("queue", "Show all current queues"),
            BotCommand("next", "Show the next Instagram Reel"),
            BotCommand("history", "Show completed video history"),
            BotCommand("jobs", "Show processing and queue jobs"),
            BotCommand("storage", "Show Telegram storage summary"),
            BotCommand("window", "View or set publishing window"),
            BotCommand("interval", "View or set Reel interval"),
            BotCommand("pause", "Pause Instagram publishing"),
            BotCommand("resume", "Resume Instagram publishing"),
            BotCommand("retry", "Retry a failed Reel"),
            BotCommand("skip", "Skip the next queued Reel"),
            BotCommand("quota", "Check Instagram publishing quota"),
            BotCommand("publish_queue", "Run an Instagram queue check"),
            BotCommand("reminder", "View or set upload reminders"),
            BotCommand("notifications", "View or set notifications"),
            BotCommand("settings", "Show bot settings"),
            BotCommand("test_telegram", "Test Telegram connection"),
            BotCommand("test_instagram", "Test Instagram API"),
            BotCommand("test_public_url", "Test public media URL"),
            BotCommand("cancel", "Cancel current video processing"),
            BotCommand("clear_completed", "Remove completed queue manifests"),
        ])
    except Exception as e:
        print(
            "⚠️ Could not register Telegram command menu: "
            f"{type(e).__name__}: {str(e)}"
        )

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

    command_handlers = [
        ("start", start),
        ("help", help_command),
        ("status", status_command),
        ("queue", queue_command),
        ("next", next_command),
        ("history", history_command),
        ("jobs", jobs_command),
        ("storage", storage_command),
        ("window", window_command),
        ("interval", interval_command),
        ("pause", pause_command),
        ("resume", resume_command),
        ("retry", retry_command),
        ("skip", skip_command),
        ("quota", quota_command),
        ("publish_queue", publish_queue_now),
        ("reminder", reminder_command),
        ("notifications", notifications_command),
        ("settings", settings_command),
        ("test_telegram", test_telegram),
        ("test_instagram", test_instagram),
        ("test_public_url", test_public_url),
        ("cancel", cancel_command),
        ("clear_completed", clear_completed_command),
    ]

    for command_name, callback in command_handlers:
        bot_application.add_handler(
            CommandHandler(
                command_name,
                callback
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
