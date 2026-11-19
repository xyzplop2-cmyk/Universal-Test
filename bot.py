# Update V4 e
import asyncio
import logging
import os
import re
import json
import base64
import hashlib
import html
import time
import datetime
import threading
import io
import gc
from collections import OrderedDict
from functools import wraps
from typing import Optional, List, Dict, Any, Tuple
from urllib.parse import urljoin

import httpx
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from supabase import create_client, Client
from supabase.lib.client_options import ClientOptions as SupabaseClientOptions

try:
    import firebase_admin
    from firebase_admin import credentials, db as firebase_db
    HAS_FIREBASE_LIB = True
except ImportError:
    HAS_FIREBASE_LIB = False

try:
    from playwright.async_api import async_playwright
    HAS_PLAYWRIGHT_LIB = True
except ImportError:
    HAS_PLAYWRIGHT_LIB = False

from flask import Flask, jsonify
from telegram import (
    Update, ReplyKeyboardMarkup, InlineKeyboardMarkup,
    LinkPreviewOptions, Message, KeyboardButton, InlineKeyboardButton,
    MessageEntity,
)
from telegram.error import RetryAfter, BadRequest
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    CallbackQueryHandler, ContextTypes, ConversationHandler, filters,
)

load_dotenv()

# ---------------- CONFIG ----------------
TOKEN = os.environ.get("BOT_TOKEN")
if not TOKEN:
    raise ValueError("BOT_TOKEN environment variable not found!")

ADMIN_ID = int(os.environ.get("ADMIN_ID", "0"))
OTP_GROUP_ID = os.environ.get("OTP_GROUP_ID", "")
DATABASE_URL = os.environ.get("DATABASE_URL")

SUPABASE_URL = os.environ.get("SUPABASE_URL")
SUPABASE_KEY = os.environ.get("SUPABASE_SERVICE_ROLE_KEY") or os.environ.get("SUPABASE_ANON_KEY")
if not SUPABASE_URL or not SUPABASE_KEY:
    raise ValueError("SUPABASE_URL and SUPABASE_SERVICE_ROLE_KEY must be set")

FIREBASE_B64 = os.environ.get("FIREBASE_BASE64")
FIREBASE_JSON_ENV = os.environ.get("FIREBASE_CONFIG_JSON")

CURRENT_DB_MODE = "Cloud (Double)"

OTP_ID_RETENTION_SECONDS = 30 * 24 * 60 * 60
CLEANUP_EVERY_N_CYCLES = 720
PROCESSED_IDS_MAX = 25000

DEFAULT_PAYOUT = 0.5
BROADCAST_CONCURRENCY = 20
BROADCAST_PER_MSG_DELAY = 0.15
BROADCAST_MAX_RETRIES = 5

FIREBASE_BACKUP_INTERVAL = 600
FIREBASE_BACKUP_BATCH_SIZE = 500
WEEKLY_RESET_CHECK_INTERVAL = 300
LEADERBOARD_CACHE_TTL = 60
MAX_KNOWN_USERS = 2000
SUPABASE_PAGE_SIZE = 1000

_BATCH_RPC_AVAILABLE = True

SEND_CONCURRENCY = 15
API_FETCH_TIMEOUT = 8.0
PANEL_INFO_CACHE_TTL = 60
API_RECORDS_PER_POLL = 200

# 🛡️ ANTI-ABUSE SYSTEM
NUMBER_CLAIM_COOLDOWN = 5.0
NUMBER_CHANGE_WINDOW = 25.0
NUMBER_CHANGE_BAN_THRESHOLD = 3

SETTINGS_CACHE = {}
SERVICES_CACHE = {}
PAYOUTS_CACHE = {}
ADMINS_CACHE = set()
PANEL_TASKS = {}
_BACKGROUND_TASKS = set()

_SEND_SEMAPHORE: Optional[asyncio.Semaphore] = None
_CHAT_LOCKS: Dict[int, asyncio.Lock] = {}
_CHAT_LOCKS_MAX = 500
_BROADCAST_SEND_LOCK: Optional[asyncio.Lock] = None
_NEXT_BROADCAST_SEND_AT = 0.0
_BOT_INFO_CACHE: Dict[str, Any] = {"username": None, "link": "https://t.me", "ts": 0.0}
_PANEL_INFO_CACHE: Dict[str, Dict[str, Any]] = {}

# 📡 LIVE OTP RECEIVERS STREAM (DB-BACKED, 24H RETENTION)
LIVE_RECEIVERS_MAX_EVENTS = 500
LIVE_RECEIVERS_RETENTION_SECONDS = 24 * 60 * 60
_LIVE_EVENTS_TABLE_MISSING = False
_LIVE_EVENTS_FALLBACK_KEY = "live_otp_events_fallback"
_LIVE_EVENTS_LOCK = threading.Lock()

_USER_IDENTITY_CACHE: Dict[int, Dict[str, Any]] = {}
_USER_IDENTITY_CACHE_TTL = 300.0
_USER_IDENTITY_CACHE_MAX = 500
_USE_PREMIUM_EMOJIS = True

# 🛡️ ANTI-ABUSE STATE
_LAST_NUMBER_CLAIM: Dict[int, float] = {}
_RECENT_NUMBER_CHANGES: Dict[int, list] = {}
_ANTI_ABUSE_STATE_MAX = 2000
_IN_MEMORY_BANNED: set = set()
_IN_MEMORY_BAN_REASONS: Dict[int, str] = {}
_NOT_BANNED_CACHE: Dict[int, float] = {}
_NOT_BANNED_CACHE_TTL = 60.0
_NOT_BANNED_CACHE_MAX = 2000

# 🔐 CAPTCHA PANEL
CAPTCHA_SESSIONS: Dict[str, dict] = {}
CAPTCHA_PANEL_STATUS: Dict[str, str] = {}
AUGESTEL_SESSIONS: Dict[str, dict] = {}
AUGESTEL_PANEL_STATUS: Dict[str, str] = {}
AUGESTEL_LOGIN_URL = "https://augestel.com/Switchfy"
AUGESTEL_DASHBOARD_URL = "https://augestel.com/Switchfy/client/live-sms"
AUGESTEL_TERMINATIONS_PATH = "/Switchfy/client/sms-statistics/terminations"
AUGESTEL_NUMBERS_PATH = "/Switchfy/client/sms-statistics/numbers"
AUGESTEL_MESSAGES_PATH = "/Switchfy/client/sms-statistics/messages"

# 🔒 FORCE JOIN CACHE
_FORCE_JOIN_CACHE: Dict[int, float] = {}
_FORCE_JOIN_CACHE_TTL = 60.0
_FORCE_JOIN_CACHE_MAX = 2000


def _prune_ts_cache(cache: dict, ttl: float, max_size: int, now: Optional[float] = None):
    if now is None:
        now = time.time()
    cutoff = now - ttl
    expired = [k for k, ts in list(cache.items()) if ts < cutoff]
    for k in expired:
        cache.pop(k, None)
    overflow = len(cache) - max_size
    if overflow > 0:
        for k in list(cache.keys())[:overflow]:
            cache.pop(k, None)


def _prune_identity_cache(now: Optional[float] = None):
    if now is None:
        now = time.time()
    cutoff = now - _USER_IDENTITY_CACHE_TTL
    expired = [k for k, v in list(_USER_IDENTITY_CACHE.items()) if float(v.get("ts", 0.0)) < cutoff]
    for k in expired:
        _USER_IDENTITY_CACHE.pop(k, None)
    overflow = len(_USER_IDENTITY_CACHE) - _USER_IDENTITY_CACHE_MAX
    if overflow > 0:
        for k in list(_USER_IDENTITY_CACHE.keys())[:overflow]:
            _USER_IDENTITY_CACHE.pop(k, None)


def prune_runtime_caches():
    now_wall = time.time()
    now_mono = time.monotonic()
    _prune_ts_cache(_NOT_BANNED_CACHE, _NOT_BANNED_CACHE_TTL, _NOT_BANNED_CACHE_MAX, now=now_wall)
    _prune_ts_cache(_FORCE_JOIN_CACHE, _FORCE_JOIN_CACHE_TTL, _FORCE_JOIN_CACHE_MAX, now=now_wall)
    _prune_identity_cache(now=now_wall)
    _prune_ts_cache(_LAST_NUMBER_CLAIM, max(NUMBER_CLAIM_COOLDOWN * 4, 60.0), _ANTI_ABUSE_STATE_MAX, now=now_mono)
    try:
        win_s = float(get_abuse_ban_window())
    except Exception:
        win_s = float(NUMBER_CHANGE_WINDOW)
    cutoff_mono = now_mono - max(win_s, 60.0)
    for k, lst in list(_RECENT_NUMBER_CHANGES.items()):
        kept = [t for t in lst if t >= cutoff_mono]
        if kept:
            _RECENT_NUMBER_CHANGES[k] = kept
        else:
            _RECENT_NUMBER_CHANGES.pop(k, None)
    overflow = len(_RECENT_NUMBER_CHANGES) - _ANTI_ABUSE_STATE_MAX
    if overflow > 0:
        for k in list(_RECENT_NUMBER_CHANGES.keys())[:overflow]:
            _RECENT_NUMBER_CHANGES.pop(k, None)
    if len(_CHAT_LOCKS) > _CHAT_LOCKS_MAX:
        for k in list(_CHAT_LOCKS.keys()):
            if not _CHAT_LOCKS[k].locked():
                _CHAT_LOCKS.pop(k, None)
                if len(_CHAT_LOCKS) <= _CHAT_LOCKS_MAX // 2:
                    break


def _get_send_semaphore() -> asyncio.Semaphore:
    global _SEND_SEMAPHORE
    if _SEND_SEMAPHORE is None:
        _SEND_SEMAPHORE = asyncio.Semaphore(SEND_CONCURRENCY)
    return _SEND_SEMAPHORE


async def _wait_for_broadcast_slot() -> None:
    global _BROADCAST_SEND_LOCK, _NEXT_BROADCAST_SEND_AT
    if _BROADCAST_SEND_LOCK is None:
        _BROADCAST_SEND_LOCK = asyncio.Lock()

    async with _BROADCAST_SEND_LOCK:
        now = time.monotonic()
        slot = max(now, _NEXT_BROADCAST_SEND_AT)
        _NEXT_BROADCAST_SEND_AT = slot + BROADCAST_PER_MSG_DELAY
        await asyncio.sleep(slot - now)


def _get_chat_lock(chat_id: int) -> asyncio.Lock:
    lock = _CHAT_LOCKS.get(chat_id)
    if lock is None:
        if len(_CHAT_LOCKS) > _CHAT_LOCKS_MAX:
            evicted = 0
            target_evict = max(1, _CHAT_LOCKS_MAX // 2)
            for k in list(_CHAT_LOCKS.keys()):
                if not _CHAT_LOCKS[k].locked():
                    _CHAT_LOCKS.pop(k, None)
                    evicted += 1
                    if evicted >= target_evict:
                        break
        lock = asyncio.Lock()
        _CHAT_LOCKS[chat_id] = lock
    return lock


async def _get_bot_info(application: Application, ttl: float = 600.0) -> Tuple[str, str]:
    now = time.time()
    if _BOT_INFO_CACHE["username"] is not None and (now - _BOT_INFO_CACHE["ts"]) < ttl:
        return _BOT_INFO_CACHE["username"], _BOT_INFO_CACHE["link"]
    try:
        info = await application.bot.get_me()
        uname = info.username or ""
        _BOT_INFO_CACHE["username"] = uname
        _BOT_INFO_CACHE["link"] = f"https://t.me/{uname}" if uname else "https://t.me"
        _BOT_INFO_CACHE["ts"] = now
    except Exception as e:
        logger.error(f"get_me error: {e}")
        if _BOT_INFO_CACHE["username"] is None:
            _BOT_INFO_CACHE["username"] = ""
            _BOT_INFO_CACHE["link"] = "https://t.me"
            _BOT_INFO_CACHE["ts"] = now
    return _BOT_INFO_CACHE["username"], _BOT_INFO_CACHE["link"]


async def _safe_send_api(bot, chat_id: int, api_method: str, **kwargs) -> bool:
    sem = _get_send_semaphore()
    lock = _get_chat_lock(chat_id)
    async with sem:
        async with lock:
            for attempt in range(BROADCAST_MAX_RETRIES + 1):
                try:
                    await getattr(bot, api_method)(chat_id=chat_id, **kwargs)
                    return True
                except RetryAfter as e:
                    if attempt == BROADCAST_MAX_RETRIES:
                        logger.error(
                            f"{api_method} rate limit retries exhausted for {chat_id}: {e}"
                        )
                        return False

                    retry_after = e.retry_after
                    if isinstance(retry_after, datetime.timedelta):
                        retry_after = retry_after.total_seconds()
                    delay = max(float(retry_after), 2 ** attempt)
                    logger.warning(
                        f"{api_method} rate limited for {chat_id}; retrying in {delay:.2f}s"
                    )
                    await asyncio.sleep(delay)
                except Exception as e:
                    logger.error(f"{api_method} error to {chat_id}: {e}")
                    return False


async def _safe_send(bot, chat_id: int, **kwargs) -> bool:
    return await _safe_send_api(bot, chat_id, "send_message", **kwargs)


async def _safe_send_rich(bot, chat_id: int, html_content: str,
                          reply_markup=None, disable_web_page_preview: bool = True) -> bool:
    """Send a Telegram Rich Message (Bot API 10.1+). Falls back gracefully."""
    api_kwargs: Dict[str, Any] = {
        "chat_id": chat_id,
        "rich_message": {"html": html_content},
    }
    if reply_markup is not None:
        try:
            api_kwargs["reply_markup"] = reply_markup.to_dict()
        except Exception:
            pass
    if disable_web_page_preview:
        api_kwargs["link_preview_options"] = {"is_disabled": True}

    try:
        await bot.do_api_request(
            "send_rich_message",
            api_kwargs=api_kwargs,
            return_type=Message,
        )
        return True
    except Exception as e:
        logger.warning(f"send_rich_message failed for {chat_id}: {e}")
        return False


class LRUSet:
    def __init__(self, maxsize: int = 20000):
        self.maxsize = maxsize
        self._data: OrderedDict = OrderedDict()

    def __contains__(self, key):
        return key in self._data

    def add(self, key):
        if key in self._data:
            self._data.move_to_end(key)
        else:
            self._data[key] = True
            if len(self._data) > self.maxsize:
                self._data.popitem(last=False)

    def __len__(self):
        return len(self._data)


class TimedLRUDict:
    def __init__(self, maxsize: int = 200000, ttl: int = OTP_ID_RETENTION_SECONDS):
        self.maxsize = maxsize
        self.ttl = ttl
        self._data: OrderedDict = OrderedDict()

    def __contains__(self, key) -> bool:
        entry = self._data.get(key)
        if entry is None:
            return False
        if time.time() - entry > self.ttl:
            self._data.pop(key, None)
            return False
        return True

    def add(self, key, ts: Optional[float] = None):
        now = ts if ts is not None else time.time()
        if key in self._data:
            self._data[key] = now
            self._data.move_to_end(key)
        else:
            self._data[key] = now
            if len(self._data) > self.maxsize:
                self._data.popitem(last=False)

    def pop(self, key, default=None):
        return self._data.pop(key, default)

    def prune(self):
        now = time.time()
        cutoff = now - self.ttl
        while self._data:
            k, ts = next(iter(self._data.items()))
            if ts < cutoff:
                self._data.popitem(last=False)
            else:
                break

    def __len__(self):
        return len(self._data)


KNOWN_USERS = LRUSet(maxsize=MAX_KNOWN_USERS)
LEADERBOARD_CACHE = {"data": None, "ts": 0}

AUGESTEL_PROCESSED_OTPS = TimedLRUDict(maxsize=10000, ttl=OTP_ID_RETENTION_SECONDS) 

logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

MENU_FILTER = filters.Regex(r"(?i)^(?:[\s\U0001F000-\U0010FFFF\u2600-\u27BF\u25A0-\u25FF\uFE0F\u200D]*)(Get Number|Profile|Wallet|Ranking|Leaderboard|Support|Admin Panel|Services|Admin Control|Global Settings|Edit Links|Edit API|Number Quantity|Broadcast|Extra|Manage Payouts|User Manager|Live Receivers|Withdraw|Back)$")


# ---------------- HELPERS ----------------
_BD_TZ = datetime.timezone(datetime.timedelta(hours=6))


def get_bd_date_str() -> str:
    return datetime.datetime.now(_BD_TZ).strftime('%Y-%m-%d')


def get_current_friday_str() -> str:
    now_bd = datetime.datetime.now(_BD_TZ)
    days_since_friday = (now_bd.weekday() - 4) % 7
    last_friday = now_bd - datetime.timedelta(days=days_since_friday)
    return last_friday.strftime('%Y-%m-%d')


def fmt_num(val) -> str:
    if val is None:
        return "0"
    try:
        val = float(val)
    except (TypeError, ValueError):
        return "0"
    if val == int(val):
        return str(int(val))
    return f"{val:.2f}".rstrip('0').rstrip('.')


def escape_md(text: str) -> str:
    if not text:
        return ""
    return str(text).replace("_", "\\_").replace("*", "\\*").replace("`", "\\`").replace("[", "\\[")

def remove_emojis(text: str) -> str:
    if not text:
        return ""
    import re
    emoji_pattern = re.compile("["
        u"\U0001F600-\U0001F64F"  # emoticons
        u"\U0001F300-\U0001F5FF"  # symbols & pictographs
        u"\U0001F680-\U0001F6FF"  # transport & map symbols
        u"\U0001F1E0-\U0001F1FF"  # flags (iOS)
        u"\U00002702-\U000027B0"
        u"\U000024C2-\U0001F251"
        "]+", flags=re.UNICODE)
    return emoji_pattern.sub(r'', text).strip()

def entities_to_tg_emoji(text: str, entities: list) -> str:
    """Converts premium emoji entities to <tg-emoji> HTML tags."""
    if not text or not entities:
        return text or ""
    
    # Sort entities by offset descending to avoid index shifting
    valid_ents = [e for e in entities if e.type == MessageEntity.CUSTOM_EMOJI]
    if not valid_ents:
        return text
    
    valid_ents.sort(key=lambda e: e.offset, reverse=True)
    text_bytes = text.encode('utf-16-le')
    
    for entity in valid_ents:
        start = entity.offset * 2
        end = (entity.offset + entity.length) * 2
        fallback = text_bytes[start:end].decode('utf-16-le', errors='ignore')
        tag = f'<tg-emoji emoji-id="{entity.custom_emoji_id}">{fallback}</tg-emoji>'
        text_bytes = text_bytes[:start] + tag.encode('utf-16-le') + text_bytes[end:]
    
    return text_bytes.decode('utf-16-le', errors='ignore')


def safe_html_escape(text: str) -> str:
    """HTML escape but preserve <tg-emoji> tags."""
    if not text:
        return ""
    parts = re.split(r'(<tg-emoji emoji-id="\d+">.*?</tg-emoji>)', str(text))
    return "".join(p if p.startswith("<tg-emoji") else html.escape(p) for p in parts)


def strip_all_emojis(text: str) -> str:
    """Strip both tg-emoji tags and regular emojis."""
    if not text:
        return ""
    t = re.sub(r'<tg-emoji.*?</tg-emoji>', '', str(text))
    return remove_emojis(t).strip()


_SC_CB_CACHE: Dict[str, Tuple[str, str]] = {}
_SC_CB_CACHE_MAX = 1000
_SRV_CB_CACHE: Dict[str, str] = {}
_SRV_CB_CACHE_MAX = 500


def _cb_clean(name: str) -> str:
    """Clean name for callback_data (removes tg-emoji to fit 64-byte limit)."""
    if not name:
        return ""
    return re.sub(r'<tg-emoji.*?</tg-emoji>', '', str(name)).strip()


def _resolve_full_key(clean: str, keys) -> str:
    """Find full key (with tg-emoji) that matches clean name."""
    for k in keys:
        if _cb_clean(k) == clean:
            return k
    return clean


def _make_srv_token(service: str) -> str:
    clean = _cb_clean(service)
    if clean and len(clean.encode("utf-8")) <= 44 and not clean.startswith("#"):
        return clean
    h = hashlib.md5(str(service).encode("utf-8")).hexdigest()[:10]
    if len(_SRV_CB_CACHE) >= _SRV_CB_CACHE_MAX and h not in _SRV_CB_CACHE:
        for k in list(_SRV_CB_CACHE.keys())[:max(1, _SRV_CB_CACHE_MAX // 2)]:
            _SRV_CB_CACHE.pop(k, None)
    _SRV_CB_CACHE[h] = service
    return f"#{h}"


def _resolve_srv_token(token: str) -> str:
    if token.startswith("#"):
        key = token[1:]
        if key in _SRV_CB_CACHE:
            return _SRV_CB_CACHE[key]
        for s in SERVICES_CACHE.keys():
            if hashlib.md5(str(s).encode("utf-8")).hexdigest()[:10] == key:
                return s
    return _resolve_full_key(token, list(SERVICES_CACHE.keys()))


def _make_sc_token(service: str, country: str) -> str:
    s_clean = _cb_clean(service)
    c_clean = _cb_clean(country)
    combined = f"{s_clean}:{c_clean}"
    if s_clean and c_clean and ":" not in s_clean and len(combined.encode("utf-8")) <= 44 and not s_clean.startswith("#"):
        return combined
    h = hashlib.md5(f"{service}\x00{country}".encode("utf-8")).hexdigest()[:10]
    if len(_SC_CB_CACHE) >= _SC_CB_CACHE_MAX and h not in _SC_CB_CACHE:
        for k in list(_SC_CB_CACHE.keys())[:max(1, _SC_CB_CACHE_MAX // 2)]:
            _SC_CB_CACHE.pop(k, None)
    _SC_CB_CACHE[h] = (service, country)
    return f"#{h}"


def _resolve_sc_token(token: str) -> Tuple[str, str]:
    if token.startswith("#"):
        key = token[1:]
        if key in _SC_CB_CACHE:
            return _SC_CB_CACHE[key]
        for s, cnts in SERVICES_CACHE.items():
            for c in cnts.keys():
                if hashlib.md5(f"{s}\x00{c}".encode("utf-8")).hexdigest()[:10] == key:
                    return s, c
    if ":" in token:
        s_tok, c_tok = token.split(":", 1)
        service = _resolve_full_key(s_tok, list(SERVICES_CACHE.keys()))
        country = _resolve_full_key(c_tok, list(SERVICES_CACHE.get(service, {}).keys()))
        return service, country
    return token, ""
        
def clean_tg_link(val: str) -> str:
    if not val:
        return "https://t.me"
    val = val.strip()
    if val.startswith("http://") or val.startswith("https://"):
        return val
    if val.startswith("t.me/"):
        return f"https://{val}"
    if val.startswith("@"):
        return f"https://t.me/{val[1:]}"
    return f"https://t.me/{val}"


def extract_otp(text: str) -> str:
    if not text:
        return "N/A"
    match = re.search(r'\b\d{4,8}\b', text)
    if match:
        return match.group(0)
    cleaned = re.sub(r'[\s/\-]', '', text)
    match = re.search(r'\d{4,8}', cleaned)
    if match:
        return match.group(0)
    return "N/A"


def create_button(text: str, callback_data: str = None, url: str = None,
                  copy_text: str = None, style: str = None, icon_custom_emoji_id: str = None) -> InlineKeyboardButton:
    final_text = str(text) if text else ""
    extracted_id = None

    match = re.search(r'<tg-emoji emoji-id="(\d+)">(.*?)</tg-emoji>', final_text)
    if match:
        prefix = final_text[:match.start()]
        if not prefix.strip():
            # Tag শুরুতেই → icon হিসেবে সেট হবে, text থেকে সম্পূর্ণ সরানো হবে
            extracted_id = match.group(1)
            final_text = final_text[match.end():]
            # বাকি থাকা tg-emoji tag → fallback emoji-তে কনভার্ট
            final_text = re.sub(r'<tg-emoji emoji-id="\d+">(.*?)</tg-emoji>',
                                r'\1', final_text).strip()
        else:
            # Tag মাঝখানে → শুধু fallback emoji-তে কনভার্ট, icon সেট হবে না
            final_text = re.sub(r'<tg-emoji emoji-id="\d+">(.*?)</tg-emoji>',
                                r'\1', final_text)

    kwargs = {"text": final_text}
    if callback_data:
        kwargs["callback_data"] = callback_data
    if url:
        kwargs["url"] = url
    if copy_text:
        kwargs["copy_text"] = {"text": copy_text}
    if style:
        kwargs["style"] = style

    final_emoji = extracted_id or icon_custom_emoji_id
    if final_emoji:
        kwargs["icon_custom_emoji_id"] = final_emoji

    return InlineKeyboardButton(**kwargs)


def _is_premium_emojis_enabled(use_premium: Optional[bool] = None) -> bool:
    if use_premium is None:
        return _USE_PREMIUM_EMOJIS
    return bool(use_premium)


def _tg_emoji(emoji_id: str, fallback: str, use_premium: Optional[bool] = None) -> str:
    if _is_premium_emojis_enabled(use_premium) and emoji_id:
        return f'<tg-emoji emoji-id="{emoji_id}">{fallback}</tg-emoji>'
    return fallback


def _unwrap_tg_emojis(text: str) -> str:
    if not text:
        return ""
    return re.sub(r'<tg-emoji emoji-id="\d+">(.*?)</tg-emoji>', r'\1', str(text))


def _clean_menu_text(text: str) -> str:
    if not text:
        return ""
    return re.sub(
        r'^[\s\U0001F000-\U0010FFFF\u2600-\u27BF\u25A0-\u25FF\uFE0F\u200D]+',
        '',
        str(text),
    ).strip()


def _admin_inline_btn(
    label: str,
    callback_data: str,
    style: str = "primary",
    emoji_id: Optional[str] = None,
    fallback_emoji: str = "",
    use_premium: Optional[bool] = None,
    emoji_after: bool = False,
) -> InlineKeyboardButton:
    premium = _is_premium_emojis_enabled(use_premium)
    if premium and emoji_id:
        return create_button(label, callback_data=callback_data, style=style, icon_custom_emoji_id=emoji_id)
    if fallback_emoji:
        btn_label = f"{label} {fallback_emoji}".strip() if emoji_after else f"{fallback_emoji} {label}".strip()
    else:
        btn_label = label
    return create_button(btn_label, callback_data=callback_data, style=style)


def _is_premium_emoji_error(err: Exception) -> bool:
    msg = str(err).lower()
    if "not modified" in msg:
        return False
    return any(tok in msg for tok in (
        "custom_emoji", "custom emoji", "icon_custom_emoji",
        "document_invalid", "emoji", "button_type_invalid",
        "tg-emoji", "premium", "sticker",
    ))


async def _reply_with_emoji_fallback(
    message,
    builder_fn,
    parse_mode: Optional[str] = None,
    link_preview_options=None,
):
    global _USE_PREMIUM_EMOJIS
    use_prem = _USE_PREMIUM_EMOJIS
    text_msg, kbd = builder_fn(use_prem)
    kwargs: Dict[str, Any] = {"reply_markup": kbd}
    if parse_mode:
        kwargs["parse_mode"] = parse_mode
    if link_preview_options is not None:
        kwargs["link_preview_options"] = link_preview_options

    try:
        return await message.reply_text(text_msg, **kwargs)
    except BadRequest as e:
        if use_prem and _is_premium_emoji_error(e):
            logger.warning(f"Premium emoji rejected on reply_text ({e}); falling back to normal emojis.")
            _USE_PREMIUM_EMOJIS = False
            text_msg, kbd = builder_fn(False)
            kwargs["reply_markup"] = kbd
            return await message.reply_text(_unwrap_tg_emojis(text_msg), **kwargs)
        raise


async def _edit_with_emoji_fallback(
    query,
    builder_fn,
    parse_mode: Optional[str] = None,
    link_preview_options=None,
) -> str:
    global _USE_PREMIUM_EMOJIS
    use_prem = _USE_PREMIUM_EMOJIS
    text_msg, kbd = builder_fn(use_prem)
    kwargs: Dict[str, Any] = {"reply_markup": kbd}
    if parse_mode:
        kwargs["parse_mode"] = parse_mode
    if link_preview_options is not None:
        kwargs["link_preview_options"] = link_preview_options

    try:
        await query.edit_message_text(text_msg, **kwargs)
        return "modified"
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return "not_modified"
        if use_prem and _is_premium_emoji_error(e):
            logger.warning(f"Premium emoji rejected on edit_message_text ({e}); falling back to normal emojis.")
            _USE_PREMIUM_EMOJIS = False
            text_msg, kbd = builder_fn(False)
            kwargs["reply_markup"] = kbd
            try:
                await query.edit_message_text(_unwrap_tg_emojis(text_msg), **kwargs)
                return "modified"
            except BadRequest as retry_err:
                if "not modified" in str(retry_err).lower():
                    return "not_modified"
                raise
        raise


def mask_number_aph(num_str: str) -> str:
    num_str = str(num_str).strip()
    if len(num_str) > 6:
        return num_str[:-6] + "APH" + num_str[-3:]
    return num_str


def mask_number_premium(num_str: str) -> Tuple[str, str]:
    """Returns (prefix_mask, number_mask) for the rich table rows."""
    digits = re.sub(r'\D', '', str(num_str))
    if not digits:
        return "XXXX", "+......XX"
    
    n = len(digits)
    if n <= 5:
        # Fallback for very short numbers
        return digits[:1] + "XXXX", "+" + digits[:1] + "......" + digits[-2:]
        
    # +213......70 format (First 3 digits + 6 dots + Last 2 digits)
    prefix = digits[:3]
    last_two = digits[-2:]
    number_mask = f"+{prefix}.............{last_two}"
    
    return "XXXX", number_mask


def mask_api_key(key: str) -> str:
    if not key:
        return "N/A"
    key_str = str(key).strip()
    length = len(key_str)
    if length > 12:
        return f"{key_str[:6]}******{key_str[-6:]}"
    elif length > 8:
        return f"{key_str[:4]}******{key_str[-4:]}"
    elif length > 4:
        return f"{key_str[:2]}******{key_str[-2:]}"
    return "******"


async def run_db(func, *args, **kwargs):
    return await asyncio.to_thread(func, *args, **kwargs)


def admin_only(func=None, *, perm: Optional[str] = None):
    def decorator(fn):
        @wraps(fn)
        async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE, *args, **kwargs):
            query = update.callback_query
            user = update.effective_user
            if not user or not (await run_db(is_admin_sync, user.id)):
                if query:
                    try:
                        await query.answer("⛔ Unauthorized!", show_alert=True)
                    except Exception:
                        pass
                return ConversationHandler.END
            if perm and not (await run_db(has_admin_perm_sync, user.id, perm)):
                if query:
                    try:
                        await query.answer("⛔ Unauthorized! Permission denied.", show_alert=True)
                    except Exception:
                        pass
                elif update.message:
                    try:
                        await update.message.reply_text("⛔ Unauthorized! You do not have permission for this action.")
                    except Exception:
                        pass
                return ConversationHandler.END
            if query:
                try:
                    await query.answer()
                except Exception:
                    pass
            return await fn(update, context, *args, **kwargs)
        return wrapper

    if func is not None and callable(func):
        return decorator(func)
    return decorator


# ============================================================
# 🛡️ ANTI-ABUSE HELPERS
# ============================================================
BANNED_TEXT = (
    "🚫 <b>You have been banned</b>\n\n"
    "You cannot get numbers or withdraw while banned.\n\n"
    "Please contact support to resolve this."
)


def _banned_keyboard():
    sp = clean_tg_link(get_setting("support", ""))
    buttons = []
    if sp and sp != "https://t.me":
        buttons.append([create_button("🎧 Contact Support", url=sp, style="primary")])
    return InlineKeyboardMarkup(buttons) if buttons else None


def is_user_banned_sync(user_id: int) -> bool:
    if user_id in _IN_MEMORY_BANNED:
        return True
    now = time.time()
    ts = _NOT_BANNED_CACHE.get(user_id)
    if ts and (now - ts) < _NOT_BANNED_CACHE_TTL:
        return False
    if len(_NOT_BANNED_CACHE) >= _NOT_BANNED_CACHE_MAX:
        _prune_ts_cache(_NOT_BANNED_CACHE, _NOT_BANNED_CACHE_TTL, _NOT_BANNED_CACHE_MAX - 1, now=now)
    try:
        res = supabase.table("users").select("is_banned").eq("user_id", user_id).limit(1).execute()
        if res.data:
            banned = bool(res.data[0].get("is_banned", False))
            if banned:
                _IN_MEMORY_BANNED.add(user_id)
                _NOT_BANNED_CACHE.pop(user_id, None)
            else:
                _NOT_BANNED_CACHE[user_id] = now
            return banned
        _NOT_BANNED_CACHE[user_id] = now
        return False
    except Exception as e:
        logger.debug(f"is_user_banned_sync error: {e}")
        _NOT_BANNED_CACHE[user_id] = now
    return False


def set_user_banned_sync(user_id: int, banned: bool, reason: str = "") -> bool:
    if banned:
        _IN_MEMORY_BANNED.add(user_id)
        if reason:
            _IN_MEMORY_BAN_REASONS[user_id] = reason
        _NOT_BANNED_CACHE.pop(user_id, None)
    else:
        _IN_MEMORY_BANNED.discard(user_id)
        _IN_MEMORY_BAN_REASONS.pop(user_id, None)
        if len(_NOT_BANNED_CACHE) >= _NOT_BANNED_CACHE_MAX:
            _prune_ts_cache(_NOT_BANNED_CACHE, _NOT_BANNED_CACHE_TTL, _NOT_BANNED_CACHE_MAX - 1)
        _NOT_BANNED_CACHE[user_id] = time.time()

    update_data = {"is_banned": banned, "dirty": True}
    if reason or not banned:
        update_data["ban_reason"] = reason if banned else ""
    try:
        supabase.table("users").update(update_data).eq("user_id", user_id).execute()
        return True
    except Exception:
        try:
            supabase.table("users").update({
                "is_banned": banned, "dirty": True,
            }).eq("user_id", user_id).execute()
            return True
        except Exception as e2:
            logger.warning(
                f"Ban NOT persisted in DB ({e2}). Add 'is_banned' (bool) and "
                f"'ban_reason' (text) columns to 'users' table for persistence."
            )
            return True


def is_abuse_autoban_enabled() -> bool:
    return get_setting("autoban_abuse_enabled", "true") == "true"


def get_abuse_ban_threshold() -> int:
    try:
        val = int(float(get_setting("autoban_abuse_threshold", str(NUMBER_CHANGE_BAN_THRESHOLD)) or NUMBER_CHANGE_BAN_THRESHOLD))
        return max(1, val)
    except Exception:
        return NUMBER_CHANGE_BAN_THRESHOLD


def get_abuse_ban_window() -> int:
    try:
        val = int(float(get_setting("autoban_abuse_window", str(int(NUMBER_CHANGE_WINDOW))) or NUMBER_CHANGE_WINDOW))
        return max(1, val)
    except Exception:
        return int(NUMBER_CHANGE_WINDOW)


def is_inactive_autoban_enabled() -> bool:
    return get_setting("autoban_inactive_enabled", "false") == "true"


def get_inactive_autoban_days() -> int:
    try:
        val = int(float(get_setting("autoban_inactive_days", "7") or 7))
        return max(1, val)
    except Exception:
        return 7


def get_inactive_autoban_min_otps() -> int:
    try:
        val = int(float(get_setting("autoban_inactive_min_otps", "10") or 10))
        return max(1, val)
    except Exception:
        return 10


def _check_number_cooldown(user_id: int) -> Tuple[bool, int]:
    now = time.monotonic()
    if len(_LAST_NUMBER_CLAIM) >= _ANTI_ABUSE_STATE_MAX:
        _prune_ts_cache(_LAST_NUMBER_CLAIM, max(NUMBER_CLAIM_COOLDOWN * 4, 60.0), _ANTI_ABUSE_STATE_MAX - 1, now=now)
    last = _LAST_NUMBER_CLAIM.get(user_id)
    if last is not None:
        elapsed = now - last
        if elapsed < NUMBER_CLAIM_COOLDOWN:
            return False, int(NUMBER_CLAIM_COOLDOWN - elapsed) + 1
    return True, 0


def _record_change_and_check_ban(user_id: int) -> Tuple[bool, int]:
    if not is_abuse_autoban_enabled():
        return False, 0
    window_s = float(get_abuse_ban_window())
    thresh = get_abuse_ban_threshold()
    now = time.monotonic()
    cutoff = now - window_s
    if len(_RECENT_NUMBER_CHANGES) >= _ANTI_ABUSE_STATE_MAX:
        for k in list(_RECENT_NUMBER_CHANGES.keys()):
            kept = [t for t in _RECENT_NUMBER_CHANGES[k] if t >= cutoff]
            if kept:
                _RECENT_NUMBER_CHANGES[k] = kept
            else:
                _RECENT_NUMBER_CHANGES.pop(k, None)
        overflow = len(_RECENT_NUMBER_CHANGES) - (_ANTI_ABUSE_STATE_MAX - 1)
        if overflow > 0:
            for k in list(_RECENT_NUMBER_CHANGES.keys())[:overflow]:
                _RECENT_NUMBER_CHANGES.pop(k, None)
    lst = [t for t in _RECENT_NUMBER_CHANGES.get(user_id, []) if t >= cutoff]
    lst.append(now)
    _RECENT_NUMBER_CHANGES[user_id] = lst
    return len(lst) >= thresh, len(lst)


async def _notify_admins_ban(context: ContextTypes.DEFAULT_TYPE,
                              user_id: int, name: str, reason: str):
    msg = (
        f"🚫 <b>AUTO-BAN TRIGGERED</b>\n\n"
        f"👤 User: <a href=\"tg://user?id={user_id}\">{html.escape(name)}</a>\n"
        f"🆔 ID: <code>{user_id}</code>\n"
        f"📝 Reason: {html.escape(reason)}\n\n"
        f"To unban: <b>User Manager → User Control</b>"
    )
    targets = set()
    if ADMIN_ID:
        targets.add(ADMIN_ID)
    for aid in ADMINS_CACHE:
        if has_admin_perm_sync(aid, "users"):
            targets.add(aid)
    for admin_id in targets:
        try:
            await context.bot.send_message(chat_id=admin_id, text=msg, parse_mode="HTML")
        except Exception as e:
            logger.warning(f"Ban notify to admin {admin_id} failed: {e}")


async def _send_banned_message(bot, chat_id: int):
    try:
        await bot.send_message(
            chat_id=chat_id, text=BANNED_TEXT,
            reply_markup=_banned_keyboard(), parse_mode="HTML",
        )
    except Exception as e:
        logger.warning(f"send banned msg failed: {e}")


def release_user_allocations_sync(user_id: int) -> int:
    try:
        rows = fetch_all_rows("allocations", "number, service, country",
                              filters={"user_id": user_id})
        if not rows:
            return 0

        groups: dict = {}
        for r in rows:
            key = (r["service"], r["country"])
            groups.setdefault(key, []).append(r["number"])

        for (srv, cnt), nums in groups.items():
            for i in range(0, len(nums), 200):
                chunk = nums[i:i + 200]
                try:
                    supabase.table("numbers").update({
                        "status": "available", "user_id": 0,
                    }).eq("service", srv).eq("country", cnt).in_("number", chunk).execute()
                except Exception as e:
                    logger.error(f"release nums update error: {e}")

        supabase.table("allocations").delete().eq("user_id", user_id).execute()

        if firebase_db_ref:
            try:
                updates = {}
                for r in rows:
                    updates[f"allocations/{r['number']}"] = None
                firebase_db_ref.reference("/").update(updates)
            except Exception:
                pass

        refresh_services_cache_sync()
        return len(rows)
    except Exception as e:
        logger.error(f"release_user_allocations_sync error: {e}")
        return 0


# ============================================================
# 🔐 AUTO CAPTCHA PANEL — Helpers & Session Store
# ============================================================
def get_panel_type(panel: dict) -> str:
    mj = panel.get("mapping_json") or ""
    if not mj:
        return "api"
    try:
        m = json.loads(mj)
        if isinstance(m, dict) and m.get("_panel_type") == "augestel":
            return "augestel"
        if isinstance(m, dict) and m.get("_panel_type") == "captcha":
            return "captcha"
        if isinstance(m, dict):
            return "custom"
    except Exception:
        pass
    return "api"


def _solve_captcha_from_html(html_text: str, soup: BeautifulSoup) -> str:
    cap = re.search(r'(\d+\s*[\+\-\*]\s*\d+)\s*[=\?:]', html_text)
    if not cap:
        cap = re.search(r'what is\s*(\d+\s*[\+\-\*]\s*\d+)', html_text, re.I)
    if not cap:
        for el in soup.find_all(["label", "div", "span", "p", "strong"]):
            t = el.get_text(separator=" ", strip=True)
            if any(op in t for op in ["+", "-", "*"]):
                m = re.search(r'(\d+\s*[\+\-\*]\s*\d+)', t)
                if m:
                    cap = m
                    break
    if not cap:
        return "0"
    m2 = re.search(r'(\d+)\s*([\+\-\*])\s*(\d+)', cap.group(1))
    if not m2:
        return "0"
    a, op, b = int(m2.group(1)), m2.group(2), int(m2.group(3))
    return str(a + b) if op == '+' else str(a - b) if op == '-' else str(a * b)


async def attempt_captcha_login(panel_id: str, panel: dict, cfg: dict) -> Tuple[bool, str]:
    login_url = (cfg.get("login_url") or "").strip()
    if not login_url.startswith("http"):
        login_url = "http://" + login_url
    if not login_url.lower().endswith('/login') and not login_url.lower().endswith('.php'):
        login_url = f"{login_url.rstrip('/')}/login"

    old = CAPTCHA_SESSIONS.pop(panel_id, None)
    if old:
        try:
            await old["client"].aclose()
        except Exception:
            pass

    client = httpx.AsyncClient(
        timeout=15.0, follow_redirects=True,
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                          "AppleWebKit/537.36 (KHTML, like Gecko) "
                          "Chrome/120.0.0.0 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        },
    )
    try:
        res = await client.get(login_url)
        soup = BeautifulSoup(res.text, 'html.parser')
        answer = _solve_captcha_from_html(res.text, soup)

        form = soup.find("form")
        if not form:
            await client.aclose()
            return False, "❌ No login form found"

        action = form.get("action")
        post_url = urljoin(login_url, action) if action else login_url

        form_data = {}
        for hidden in form.find_all("input", type="hidden"):
            nm = hidden.get("name")
            if nm:
                form_data[nm] = hidden.get("value") or ""

        def _m(keys):
            def _c(v):
                if not v:
                    return False
                v = v.lower()
                return any(k in v for k in keys)
            return _c

        user_input = (
            form.find("input", {"name": _m(["user", "email", "id"])}) or
            form.find("input", {"type": "text", "placeholder": _m(["user", "email"])}) or
            form.find("input", {"type": "text"})
        )
        pass_input = (
            form.find("input", {"name": _m(["pass", "password", "passwd"])}) or
            form.find("input", {"type": "password"})
        )
        captcha_input = (
            form.find("input", {"placeholder": _m(["answer", "ans", "code", "verification", "value", "captcha"])}) or
            form.find("input", {"name": _m(["ans", "captcha", "ver", "code"])})
        )

        user_field = user_input.get("name") if user_input else "username"
        pass_field = pass_input.get("name") if pass_input else "password"
        captcha_field = captcha_input.get("name") if captcha_input else "answer"

        form_data[user_field] = cfg.get("username", "")
        form_data[pass_field] = cfg.get("password", "")
        if captcha_input:
            form_data[captcha_field] = answer

        login_req = await client.post(post_url, data=form_data)

        msg_link = (cfg.get("msg_link") or "").strip()
        if msg_link and not msg_link.startswith("http"):
            msg_link = "http://" + msg_link
        check_url = msg_link or f"{login_url.split('/login')[0]}/client/SMSCDRStats"
        check_res = await client.get(check_url)

        ok_keywords = [
            'logout', 'log out', 'signout', 'sign out',
            'sms reports', 'dashboard', 'cdrs',
            'welcome', 'profile', 'panel', 'inbox',
            'number', 'report', 'home', 'account',
            'client', 'smscdr', 'numberpanel',
        ]
        combined = (login_req.text + check_res.text).lower()
        if any(kw in combined for kw in ok_keywords):
            CAPTCHA_SESSIONS[panel_id] = {
                "client": client,
                "login_url": login_url,
                "check_url": check_url,
                "last_login": time.time(),
            }
            return True, "✅ Active & Fetching"

        uf = user_input.get("name") if user_input else "NOT FOUND"
        pf = pass_input.get("name") if pass_input else "NOT FOUND"
        cf = captcha_input.get("name") if captcha_input else "none"
        await client.aclose()
        return False, f"❌ Login Failed (user={uf}, pass={pf}, captcha={cf})"

    except Exception as e:
        try:
            await client.aclose()
        except Exception:
            pass
        return False, f"❌ Error: {str(e)[:80]}"


def _parse_captcha_html_table(soup, num_idx, msg_idx, num_name, msg_name,
                              dt_idx=-1, dt_name="") -> list:
    results = []
    for table in soup.find_all('table'):
        rows = table.find_all('tr')
        if not rows:
            continue
        final_n, final_m = num_idx, msg_idx
        final_dt = dt_idx

        header_cells = rows[0].find_all(['th', 'td'])
        for i, cell in enumerate(header_cells):
            t = cell.get_text(strip=True).lower()
            if num_name in t:
                final_n = i
            if msg_name in t:
                final_m = i
            if dt_name and dt_name.lower() in t:
                final_dt = i

        for row in rows:
            cols = row.find_all(['td', 'th'])
            if all(c.name == 'th' for c in cols):
                continue

            if len(cols) > max(final_n, final_m):
                num_text = cols[final_n].get_text(separator=" ", strip=True)
                msg_text = cols[final_m].get_text(separator=" ", strip=True)
                dt_text = ""
                if 0 <= final_dt < len(cols):
                    dt_text = cols[final_dt].get_text(separator=" ", strip=True)

                clean_num = re.sub(r'\D', '', num_text)

                if clean_num and 5 <= len(clean_num) <= 18 and len(msg_text) > 0:
                    results.append({
                        "num": clean_num, "message": msg_text,
                        "dt": dt_text, "payout": 1, "cli": "",
                    })
    return results


async def fetch_captcha_panel_data(panel_id: str, cfg: dict) -> Tuple[list, str]:
    sess = CAPTCHA_SESSIONS.get(panel_id)
    if not sess:
        return [], "❌ No active session"

    client = sess["client"]
    check_url = sess["check_url"]

    try:
        res = await client.get(check_url)
        html_text = res.text

        lower = html_text.lower()
        if ("login" in lower or "signin" in lower) or any(
            x in html_text for x in ["Sign in to your account", "Please sign in", "Welcome back!"]
        ):
            return [], "❌ Session expired"

        soup = BeautifulSoup(html_text, 'html.parser')

        s_ajax = ""
        for script in soup.find_all("script"):
            st = script.string or ""
            m = re.search(r'sAjaxSource"?\s*:\s*"([^"]+)"', st)
            if m:
                s_ajax = m.group(1); break
            m = re.search(r'["\']ajax["\']\s*:\s*["\']([^"\']+)["\']', st)
            if m:
                s_ajax = m.group(1); break
            m = re.search(r'["\']?ajax["\']?\s*:\s*\{[^}]*["\']?url["\']?\s*:\s*["\']([^"\']+)["\']', st)
            if m:
                s_ajax = m.group(1); break
            if 'DataTable' in st or 'dataTable' in st:
                m = re.search(r'"url"\s*:\s*"([^"]+)"', st)
                if m:
                    s_ajax = m.group(1); break

        detected_cols = 9
        for table in soup.find_all('table'):
            hr = table.find_all('tr')
            if hr:
                first = hr[0].find_all(['th', 'td'])
                if len(first) > detected_cols:
                    detected_cols = len(first)
                    break

        num_idx = int(cfg.get("num_col_idx", 1)) - 1 if cfg.get("num_col_idx") else 1
        msg_idx = int(cfg.get("msg_col_idx", 2)) - 1 if cfg.get("msg_col_idx") else 2
        num_name = (cfg.get("num_col_name") or "number").lower()
        msg_name = (cfg.get("msg_col_name") or "message").lower()

        dt_idx = -1
        dt_name = (cfg.get("dt_col_name") or "").lower().strip()
        if cfg.get("dt_col_idx") is not None:
            try:
                dt_val = int(cfg.get("dt_col_idx"))
                if dt_val > 0:
                    dt_idx = dt_val - 1
            except (ValueError, TypeError):
                pass

        results = []

        html_results = _parse_captcha_html_table(
            soup, num_idx, msg_idx, num_name, msg_name,
            dt_idx=dt_idx, dt_name=dt_name,
        )
        if html_results:
            results = html_results

        if not results and s_ajax:
            base_url = (cfg.get("login_url") or "").split("/client")[0].split("/login")[0].strip()
            if not base_url.startswith("http"):
                base_url = "http://" + base_url
            if s_ajax.startswith("http"):
                full_url = s_ajax
            elif s_ajax.startswith("/"):
                full_url = f"{base_url}{s_ajax}"
            else:
                idx = check_url.rfind("/")
                cur_dir = check_url[:idx] if idx > 0 else check_url.rstrip("/")
                full_url = f"{cur_dir}/{s_ajax}"

            if "iDisplayLength" not in full_url:
                col_search = "&".join([
                    f"sSearch_{i}=&bRegex_{i}=false&bSearchable_{i}=true&bSortable_{i}=true"
                    for i in range(detected_cols)
                ])
                qp = (
                    f"sEcho=1&iColumns={detected_cols}&iDisplayStart=0&iDisplayLength=9999"
                    f"&sSearch=&bRegex=false&iSortingCols=1&iSortCol_0=0&sSortDir_0=desc&{col_search}"
                )
                div = "&" if "?" in full_url else "?"
                full_url += f"{div}{qp}"

            ajax_headers = {
                "Referer": check_url,
                "X-Requested-With": "XMLHttpRequest",
            }

            try:
                ajax_res = await client.get(full_url, headers=ajax_headers)
                if ajax_res.text.strip():
                    data_dict = ajax_res.json()
                    rows = data_dict.get("aaData") or data_dict.get("data") or []

                    for row_val in rows:
                        if isinstance(row_val, list):
                            if len(row_val) > max(num_idx, msg_idx):
                                num_val = row_val[num_idx]
                                msg_val = row_val[msg_idx]
                                dt_val_str = ""
                                if 0 <= dt_idx < len(row_val):
                                    dt_val_str = str(row_val[dt_idx])

                                clean_num = re.sub(r'\D', '', str(num_val))
                                if clean_num and 5 <= len(clean_num) <= 18 and len(str(msg_val).strip()) > 0:
                                    results.append({
                                        "num": clean_num, "message": str(msg_val),
                                        "dt": dt_val_str, "payout": 1, "cli": "",
                                    })
                        elif isinstance(row_val, dict):
                            num_val = row_val.get("number") or row_val.get(num_name) or row_val.get(str(num_idx))
                            msg_val = row_val.get("sms") or row_val.get(msg_name) or row_val.get(str(msg_idx))
                            dt_val_str = row_val.get("date") or row_val.get(dt_name) or row_val.get(str(dt_idx), "")

                            if num_val and msg_val:
                                clean_num = re.sub(r'\D', '', str(num_val))
                                if clean_num and 5 <= len(clean_num) <= 18 and len(str(msg_val).strip()) > 0:
                                    results.append({
                                        "num": clean_num, "message": str(msg_val),
                                        "dt": str(dt_val_str), "payout": 1, "cli": "",
                                    })
            except Exception:
                pass

        return results, "✅ Active & Fetching"

    except Exception as e:
        return [], f"❌ Fetch error: {str(e)[:80]}"

def _make_otp_hash(number: str, msg: str, dt: str) -> str:
    """Creates a unique hash for deduplication"""
    # Clean dt to only digits (YYYYMMDDHHMMSS)
    clean_dt = re.sub(r'\D', '', str(dt))[:14] # 👈 [:14] যোগ করা হলো
    raw = f"{number}|{msg.strip()[:100]}|{clean_dt}"
    return hashlib.sha256(raw.encode('utf-8')).hexdigest()

async def _process_hybrid_item(panel_id: str, item: dict, context_holder: dict, source: str = "Unknown"):
    """Processes items from either WebSocket or API, handles deduplication."""
    num = re.sub(r'\D', '', str(item.get("num", "")))
    msg = str(item.get("message", "")).strip()
    dt = str(item.get("dt", ""))
    cli = str(item.get("cli", ""))
    payout = item.get("payout", 1)
    
    if not num or not msg:
        return

    # Deduplication Check
    otp_hash = _make_otp_hash(num, msg, dt)
    if otp_hash in AUGESTEL_PROCESSED_OTPS:
        logger.info(f"[{source}] Duplicate skipped: {num} | {dt}") 
        return 
    
    AUGESTEL_PROCESSED_OTPS.add(otp_hash)
    logger.info(f"[{source}] New OTP Captured: {num} | {dt} | CLI: {cli}") # 👈 এখানে সোর্স দেখতে পাবেন
    
    final_item = {
        "num": num,
        "message": msg,
        "dt": dt,
        "payout": payout,
        "cli": cli,
        "panel_id": panel_id,
        "source": source, # 👈 সোর্স সেভ করা হলো
    }
    
    queue = context_holder.get("queue")
    if queue:
        await queue.put(final_item)

    event = context_holder.get("ws_event")
    if event:
        event.set()

def _augestel_ws_listener(ws, panel_id: str):
    """Listens to live-sms websocket payload (Synchronous callback for Playwright)"""
    # 👈 এখানে সব ওয়েবসকেট URL দেখতে পাবেন
    logger.info(f"🔗 WebSocket Detected for panel {panel_id} | URL: {ws.url}")
    
    def on_message(payload):
        try:
            text = payload if isinstance(payload, str) else payload.decode('utf-8')
            # 👈 র ডাটা আসছে কি না দেখার জন্য ডিবাগ লগ (শুধু চেক করার জন্য)
            logger.debug(f"[WS RAW DATA]: {text[:200]}") 
            
            data = json.loads(text)
            
            if data.get("type") != "new_message":
                return
                
            msg_data = data.get("data", {})
            raw_num = str(msg_data.get("destination_address") or "")
            msg_content = str(msg_data.get("message_content") or "")
            timestamp = str(msg_data.get("timestamp") or "")
            source_cli = str(msg_data.get("source_address") or "")
            sell_rate = str(msg_data.get("sell_rate") or "1")
            
            if not raw_num or not msg_content:
                return
                
            item = {
                "num": raw_num,
                "message": msg_content,
                "dt": timestamp,
                "cli": source_cli,
                "payout": sell_rate,
            }
            
            ctx = AUGESTEL_SESSIONS.get(str(panel_id), {}).get("state", {})
            asyncio.create_task(_process_hybrid_item(str(panel_id), item, ctx, source="WS"))
            
        except Exception as e:
            logger.error(f"WS Parse Error: {e}")

    ws.on("framereceived", on_message)

async def _augestel_api_poller(panel_id: str, api_key: str, interval: float, ctx_holder: dict):
    """Runs in background, polls API every X seconds as backup"""
    url = "https://augestel.com/api/v1/iprn/messages"
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Accept": "application/json"
    }
    
    while AUGESTEL_SESSIONS.get(str(panel_id)):
        try:
            today = datetime.datetime.now().strftime("%Y-%m-%d")
            params = {
                "start_date": today,
                "end_date": today,
                "per_page": 200
            }
            
            async with httpx.AsyncClient(timeout=15.0) as client:
                res = await client.get(url, headers=headers, params=params)
                
                if res.status_code == 429:
                    retry_after = int(res.headers.get("Retry-After", 15))
                    logger.warning(f"API Rate limit hit. Waiting {retry_after}s")
                    await asyncio.sleep(retry_after)
                    continue
                    
                if res.status_code == 200:
                    data = res.json()
                    if data.get("success"):
                        for msg in data.get("data", []):
                            item = {
                                "num": str(msg.get("number", "")),
                                "message": str(msg.get("message", "")),
                                "dt": str(msg.get("received_at", "")),
                                "cli": str(msg.get("source", "")),
                                "payout": str(msg.get("rate", "1"))
                            }
                            await _process_hybrid_item(str(panel_id), item, ctx_holder, source="API")
                            
        except Exception as e:
            logger.error(f"API Poller Error: {e}")
            
        await asyncio.sleep(interval)
async def _augestel_close_session(panel_id: str):
    sess = AUGESTEL_SESSIONS.pop(str(panel_id), None)
    if not sess:
        return
    try:
        page = sess.get("page")
        if page:
            try:
                await page.close()
            except Exception:
                pass
    except Exception:
        pass
    try:
        ctx = sess.get("context")
        if ctx:
            try:
                await ctx.close()
            except Exception:
                pass
    except Exception:
        pass
    try:
        browser = sess.get("browser")
        if browser:
            try:
                await browser.close()
            except Exception:
                pass
    except Exception:
        pass
    try:
        pw = sess.get("pw")
        if pw:
            try:
                await pw.stop()
            except Exception:
                pass
    except Exception:
        pass

async def _augestel_login(panel_id: str, panel: dict, cfg: dict) -> Tuple[bool, str]:
    if not HAS_PLAYWRIGHT_LIB:
        return False, "Playwright not installed"
    
    email = str(cfg.get("email") or "").strip()
    password = str(cfg.get("password") or "")
    api_key = str(cfg.get("api_key") or "")
    login_url = str(cfg.get("login_url") or AUGESTEL_LOGIN_URL).strip()
    dashboard_url = str(cfg.get("dashboard_url") or AUGESTEL_DASHBOARD_URL).strip()
    
    if not email or not password:
        return False, "Missing email or password"
        
    await _augestel_close_session(panel_id)
    pw = None
    browser = None
    
    try:
        pw = await async_playwright().start()
        browser = await pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-setuid-sandbox", "--disable-dev-shm-usage", "--disable-blink-features=AutomationControlled"]
        )
        context = await browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
            viewport={"width": 1280, "height": 800},
        )
        page = await context.new_page()
        
        # Start Listening for WebSockets BEFORE navigation
        context.on("websocket", lambda ws: _augestel_ws_listener(ws, str(panel_id)))

        page = await context.new_page()
        page.on("websocket", lambda ws: _augestel_ws_listener(ws, str(panel_id)))
        
        await page.goto(login_url, wait_until="domcontentloaded", timeout=60000)
        await page.wait_for_timeout(4000)
        
        email_input = page.get_by_placeholder("you@company.com").or_(page.get_by_label("Email address")).or_(page.locator("input:visible").nth(0)).first
        password_input = page.locator('input[type="password"]:visible').or_(page.get_by_label("Password")).first
        
        await email_input.wait_for(state="visible", timeout=30000)
        await email_input.fill(email)
        await password_input.fill(password)
        await page.get_by_role("button", name="Sign in").click()
        
        try:
            await page.wait_for_url("**/Switchfy/test/**", timeout=60000)
        except Exception:
            if page.url.rstrip("/") == login_url.rstrip("/"):
                raise RuntimeError("Login failed. Still on login page")
                
        await page.goto(dashboard_url, wait_until="domcontentloaded", timeout=60000)
        await page.wait_for_timeout(3000)
        logger.info(f"✅ Augestel Dashboard loaded for {panel_id}. Waiting for WebSocket frames...")
        
        # Auto Refresh Mechanism (Every 5m)
        async def periodic_refresh():
            while AUGESTEL_SESSIONS.get(str(panel_id)):
                await asyncio.sleep(300) # 5m
                logger.info(f"Refreshing Augestel Page for {panel_id}")
                try:
                    p = AUGESTEL_SESSIONS.get(str(panel_id), {}).get("page")
                    if p:
                        await p.reload(wait_until="domcontentloaded")
                except Exception as e:
                    logger.error(f"Auto Refresh failed: {e}")
                    
        asyncio.create_task(periodic_refresh())
        
        # Queue for unified processing
        otp_queue = asyncio.Queue()
        ws_event = asyncio.Event()
        state = {
            "queue": otp_queue,
            "ws_event": ws_event,
            "raw_items_queue": otp_queue
        }
        
        AUGESTEL_SESSIONS[str(panel_id)] = {
            "pw": pw,
            "browser": browser,
            "context": context,
            "page": page,
            "state": state,
            "last_login": time.time(),
        }
        
        # Start the API Poller as Backup
        if api_key:
            p_interval = panel.get("polling_interval", 13.0)
            asyncio.create_task(_augestel_api_poller(str(panel_id), api_key, p_interval, state))
            
        return True, "Active & Fetching (WS + API)"
        
    except Exception as e:
        try:
            if browser: await browser.close()
            if pw: await pw.stop()
        except Exception:
            pass
        return False, f"Error: {str(e)[:80]}"

async def fetch_augestel_panel_data(panel_id: str, cfg: dict) -> Tuple[list, str]:
    """This function is called by the main loop to get new OTPs"""
    sess = AUGESTEL_SESSIONS.get(str(panel_id))
    if not sess:
        ok, status = await _augestel_login(str(panel_id), {}, cfg)
        if not ok:
            return [], status
        sess = AUGESTEL_SESSIONS.get(str(panel_id))
        if not sess:
            return [], "Login failed"
            
    try:
        queue = sess.get("state", {}).get("queue")
        items = []
        
        # Empty the queue (non-blocking)
        while not queue.empty():
            try:
                items.append(queue.get_nowait())
            except asyncio.QueueEmpty:
                break
                
        return items, "Active & Fetching"
    except Exception as e:
        return [], f"Fetch error: {str(e)[:80]}"


def _get_json_path(obj, path):
    if not path:
        return None
    path = str(path).strip()
    if not path:
        return None
    cur = obj
    for part in path.split("."):
        part = part.strip()
        if not part:
            continue
        if isinstance(cur, dict):
            cur = cur.get(part)
        elif isinstance(cur, list):
            try:
                idx = int(part.strip("[]"))
                cur = cur[idx] if 0 <= idx < len(cur) else None
            except (ValueError, IndexError):
                return None
        else:
            return None
        if cur is None:
            return None
    return cur


def apply_custom_mapping(res_data, mapping: dict) -> list:
    if not isinstance(mapping, dict):
        return []

    status_path = mapping.get("status_path")
    if status_path:
        actual = _get_json_path(res_data, status_path)
        expected = str(mapping.get("status_value", "success")).strip()
        if str(actual).strip().lower() != expected.lower():
            return []

    data_path = mapping.get("data_path", "data")
    data = _get_json_path(res_data, data_path)
    if not isinstance(data, list):
        return []

    num_path = mapping.get("num_path", "num")
    msg_path = mapping.get("msg_path", "message")
    dt_path = mapping.get("dt_path", "dt")
    payout_path = mapping.get("payout_path")
    cli_path = mapping.get("cli_path")

    items = []
    for entry in data:
        if not isinstance(entry, dict):
            continue
        num = _get_json_path(entry, num_path)
        msg = _get_json_path(entry, msg_path)
        dt = _get_json_path(entry, dt_path) or ""
        if payout_path:
            payout = _get_json_path(entry, payout_path)
            if payout is None:
                payout = 0
        else:
            payout = 1
        cli = _get_json_path(entry, cli_path) if cli_path else ""

        items.append({
            "num": str(num or "").strip(),
            "message": str(msg or ""),
            "dt": str(dt or ""),
            "payout": str(payout),
            "cli": str(cli or ""),
        })
    return items


def fetch_all_rows(table: str, columns: str,
                   filters: dict = None,
                   order_col: str = None, order_desc: bool = False,
                   in_filter: tuple = None,
                   chunk_size: int = SUPABASE_PAGE_SIZE) -> list:
    all_rows = []
    try:
        if in_filter:
            col, values = in_filter
            for i in range(0, len(values), chunk_size):
                chunk = values[i:i + chunk_size]
                offset = 0
                while True:
                    q = supabase.table(table).select(columns).in_(col, chunk)
                    if filters:
                        for k, v in filters.items():
                            q = q.eq(k, v)
                    if order_col:
                        q = q.order(order_col, desc=order_desc)
                    r = q.range(offset, offset + chunk_size - 1).execute()
                    if not r.data:
                        break
                    all_rows.extend(r.data)
                    if len(r.data) < chunk_size:
                        break
                    offset += chunk_size
            return all_rows

        offset = 0
        while True:
            q = supabase.table(table).select(columns)
            if filters:
                for k, v in filters.items():
                    q = q.eq(k, v)
            if order_col:
                q = q.order(order_col, desc=order_desc)
            r = q.range(offset, offset + chunk_size - 1).execute()
            if not r.data:
                break
            all_rows.extend(r.data)
            if len(r.data) < chunk_size:
                break
            offset += chunk_size
    except Exception as e:
        logger.error(f"fetch_all_rows({table}) error: {e}")
    return all_rows


supabase: Optional[Client] = None


def init_supabase() -> bool:
    global supabase
    try:
        options = SupabaseClientOptions(auto_refresh_token=False, persist_session=False)
        supabase = create_client(SUPABASE_URL, SUPABASE_KEY, options=options)
        logger.info("Supabase client initialized")
        return True
    except Exception as e:
        logger.error(f"Supabase init error: {e}")
        return False


firebase_db_ref = None


def init_firebase() -> bool:
    global firebase_db_ref
    if not HAS_FIREBASE_LIB:
        logger.info("Firebase Admin SDK not installed — backup disabled")
        return False
    if firebase_admin._apps:
        firebase_db_ref = firebase_db
        return True

    cred_dict = None
    try:
        if FIREBASE_B64:
            cred_dict = json.loads(base64.b64decode(FIREBASE_B64).decode('utf-8'))
        elif FIREBASE_JSON_ENV:
            cred_dict = json.loads(FIREBASE_JSON_ENV)
            if "private_key" in cred_dict:
                cred_dict["private_key"] = cred_dict["private_key"].replace("\\n", "\n")
        if cred_dict:
            cred = credentials.Certificate(cred_dict)
            options = {}
            if DATABASE_URL:
                options['databaseURL'] = DATABASE_URL
            firebase_admin.initialize_app(cred, options if options else None)
            firebase_db_ref = firebase_db
            logger.info("Firebase connected (backup mode)")
            return True
        else:
            logger.info("No Firebase credentials — backup disabled")
            return False
    except Exception as e:
        logger.error(f"Firebase Init Error: {e}")
        return False


def get_payout_sync(service: str, country: str) -> float:
    if not service or not country:
        return DEFAULT_PAYOUT
    if service in PAYOUTS_CACHE and country in PAYOUTS_CACHE[service]:
        return float(PAYOUTS_CACHE[service][country])
    try:
        res = supabase.table("payouts").select("payout").eq("service_name", service).eq("country_name", country).execute()
        if res.data and res.data[0].get("payout") is not None:
            fval = float(res.data[0]["payout"])
            PAYOUTS_CACHE.setdefault(service, {})[country] = fval
            return fval
    except Exception as e:
        logger.error(f"Supabase get payout error: {e}")
    return DEFAULT_PAYOUT


def set_payout_sync(service: str, country: str, amount: float):
    if not service or not country:
        return
    try:
        amount = float(amount)
        if amount < 0:
            amount = 0.0
    except (TypeError, ValueError):
        amount = DEFAULT_PAYOUT

    PAYOUTS_CACHE.setdefault(service, {})[country] = amount
    try:
        supabase.table("payouts").upsert({
            "service_name": service, "country_name": country, "payout": amount
        }).execute()
    except Exception as e:
        logger.error(f"Supabase set payout error: {e}")
    if firebase_db_ref:
        try:
            firebase_db_ref.reference(f"payouts/{service}/{country}").set(amount)
        except Exception as e:
            logger.error(f"Firebase set payout error: {e}")


def refresh_payouts_cache_sync():
    global PAYOUTS_CACHE
    new_cache = {}
    try:
        rows = fetch_all_rows("payouts", "service_name, country_name, payout")
        for r in rows:
            new_cache.setdefault(r["service_name"], {})[r["country_name"]] = (
                float(r["payout"]) if r.get("payout") is not None else DEFAULT_PAYOUT
            )
    except Exception as e:
        logger.error(f"Supabase payouts cache load error: {e}")
    PAYOUTS_CACHE = new_cache


def get_withdraw_methods_sync() -> list:
    try:
        rows = fetch_all_rows("withdraw_methods", "name")
        return [r["name"] for r in rows]
    except Exception as e:
        logger.error(f"Supabase get withdraw methods error: {e}")
        return []


def add_withdraw_method_sync(name: str):
    name = name.strip()
    if not name:
        return
    try:
        supabase.table("withdraw_methods").upsert({"name": name}).execute()
        if firebase_db_ref:
            firebase_db_ref.reference(f"withdraw_methods/{name}").set(True)
    except Exception as e:
        logger.error(f"Supabase add withdraw method error: {e}")


def delete_withdraw_method_sync(name: str):
    try:
        supabase.table("withdraw_methods").delete().eq("name", name).execute()
        if firebase_db_ref:
            firebase_db_ref.reference(f"withdraw_methods/{name}").delete()
    except Exception as e:
        logger.error(f"Supabase delete withdraw method error: {e}")


def deduct_user_balance_sync(user_id: int, amount: float) -> bool:
    try:
        res = supabase.rpc("deduct_user_balance", {
            "p_user_id": user_id, "p_amount": amount,
        }).execute()
        return bool(res.data)
    except Exception as e:
        logger.error(f"Supabase deduct balance RPC error: {e}")
        prof = get_user_profile_sync(user_id)
        if prof["balance"] < amount:
            return False
        try:
            supabase.table("users").update({
                "balance": prof["balance"] - amount, "dirty": True,
            }).eq("user_id", user_id).execute()
            return True
        except Exception:
            return False


def refund_user_balance_sync(user_id: int, amount: float):
    prof = get_user_profile_sync(user_id)
    try:
        supabase.table("users").update({
            "balance": prof["balance"] + amount, "dirty": True,
        }).eq("user_id", user_id).execute()
    except Exception as e:
        logger.error(f"Supabase refund balance error: {e}")


def create_withdraw_request_sync(user_id: int, method: str, wallet_number: str,
                                 amount: float, username: str = "") -> int:
    ts = int(time.time())
    base_data = {
        "user_id": user_id, "method": method, "wallet_number": wallet_number,
        "amount": amount, "status": "pending", "reject_reason": "", "created_at": ts,
    }
    username = (username or "").strip().lstrip("@")

    try:
        data = dict(base_data)
        if username:
            data["username"] = username
        try:
            res = supabase.table("withdraw_requests").insert(data).execute()
        except Exception as e:
            if "username" in str(e).lower() and "column" in str(e).lower():
                res = supabase.table("withdraw_requests").insert(base_data).execute()
            else:
                raise
        req_id = res.data[0]["id"]
        if firebase_db_ref:
            try:
                firebase_db_ref.reference(f"withdraw_requests/{req_id}").set({
                    "id": req_id, "user_id": user_id, "method": method,
                    "wallet_number": wallet_number, "amount": amount,
                    "status": "pending", "reject_reason": "", "created_at": ts,
                    "username": username,
                })
            except Exception:
                pass
        return req_id
    except Exception as e:
        logger.error(f"Supabase create withdraw req error: {e}")
        return 0


def get_all_withdraw_requests_sync() -> list:
    try:
        try:
            rows = fetch_all_rows(
                "withdraw_requests",
                "id, user_id, username, method, wallet_number, amount, status, reject_reason, created_at",
                order_col="id", order_desc=False,
            )
            if not rows:
                raise Exception("empty_or_missing_column")
        except Exception:
            rows = fetch_all_rows(
                "withdraw_requests",
                "id, user_id, method, wallet_number, amount, status, reject_reason, created_at",
                order_col="id", order_desc=False,
            )
        return [{
            "id": r["id"], "user_id": r["user_id"], "method": r["method"],
            "wallet_number": r["wallet_number"], "amount": r["amount"],
            "status": r["status"], "reject_reason": r.get("reject_reason", ""),
            "created_at": r.get("created_at", 0),
            "username": r.get("username") or "",
        } for r in rows]
    except Exception as e:
        logger.error(f"Supabase fetch withdraw reqs error: {e}")
        return []


def get_withdraw_request_by_id_sync(req_id: int):
    try:
        try:
            res = supabase.table("withdraw_requests").select("id, user_id, username, method, wallet_number, amount, status, reject_reason, created_at").eq("id", req_id).execute()
        except Exception:
            res = supabase.table("withdraw_requests").select("*").eq("id", req_id).execute()
        if res.data:
            r = res.data[0]
            return {
                "id": r["id"], "user_id": r["user_id"], "method": r["method"],
                "wallet_number": r["wallet_number"], "amount": r["amount"],
                "status": r["status"], "reject_reason": r.get("reject_reason", ""),
                "created_at": r.get("created_at", 0),
                "username": r.get("username") or "",
            }
    except Exception as e:
        logger.error(f"Supabase fetch single withdraw req error: {e}")
    return None


def atomic_transition_withdraw_status_sync(req_id: int, from_status: str,
                                           to_status: str, reject_reason: str = "") -> bool:
    try:
        res = supabase.rpc("transition_withdraw", {
            "p_req_id": req_id, "p_from_status": from_status,
            "p_to_status": to_status, "p_reject_reason": reject_reason,
        }).execute()
        if bool(res.data):
            if firebase_db_ref:
                try:
                    firebase_db_ref.reference(f"withdraw_requests/{req_id}").update({
                        "status": to_status, "reject_reason": reject_reason,
                    })
                except Exception:
                    pass
            return True
        return False
    except Exception as e:
        err_str = str(e)
        rpc_missing = ("does not exist" in err_str or "PGRST202" in err_str
                       or "Could not find" in err_str or "not find the function" in err_str)
        if rpc_missing:
            logger.warning("transition_withdraw RPC not found — using UPDATE fallback")
        else:
            logger.error(f"transition_withdraw RPC error: {e}")

    try:
        res = (supabase.table("withdraw_requests")
               .update({"status": to_status, "reject_reason": reject_reason})
               .eq("id", req_id).eq("status", from_status).execute())
        updated = bool(res.data) and len(res.data) > 0
        if updated and firebase_db_ref:
            try:
                firebase_db_ref.reference(f"withdraw_requests/{req_id}").update({
                    "status": to_status, "reject_reason": reject_reason,
                })
            except Exception:
                pass
        return updated
    except Exception as e2:
        logger.error(f"Fallback withdraw transition error: {e2}")
        return False


def update_withdraw_status_sync(req_id: int, status: str, reject_reason: str = ""):
    try:
        supabase.table("withdraw_requests").update({
            "status": status, "reject_reason": reject_reason,
        }).eq("id", req_id).execute()
        if firebase_db_ref:
            firebase_db_ref.reference(f"withdraw_requests/{req_id}").update({
                "status": status, "reject_reason": reject_reason,
            })
    except Exception as e:
        logger.error(f"Supabase update withdraw status error: {e}")


def get_user_identities_batch_sync(user_ids: list) -> Dict[int, Dict[str, str]]:
    if not user_ids:
        return {}
    now = time.time()
    result: Dict[int, Dict[str, str]] = {}
    missing = []
    for raw_uid in user_ids:
        try:
            uid = int(raw_uid)
        except (TypeError, ValueError):
            continue
        cached = _USER_IDENTITY_CACHE.get(uid)
        if cached and (now - cached.get("ts", 0.0)) < _USER_IDENTITY_CACHE_TTL:
            result[uid] = {
                "first_name": cached.get("first_name", ""),
                "username": cached.get("username", ""),
            }
        else:
            missing.append(uid)

    if missing:
        if len(_USER_IDENTITY_CACHE) >= _USER_IDENTITY_CACHE_MAX:
            _prune_identity_cache(now=now)
        try:
            for i in range(0, len(missing), 500):
                chunk = missing[i:i + 500]
                try:
                    res = supabase.table("users").select("user_id, username, first_name").in_("user_id", chunk).execute()
                    for r in res.data or []:
                        uid = int(r["user_id"])
                        ident = {
                            "first_name": str(r.get("first_name") or "").strip(),
                            "username": str(r.get("username") or "").strip().lstrip("@"),
                        }
                        result[uid] = ident
                        _USER_IDENTITY_CACHE[uid] = {**ident, "ts": now}
                except Exception:
                    res = supabase.table("users").select("user_id, first_name").in_("user_id", chunk).execute()
                    for r in res.data or []:
                        uid = int(r["user_id"])
                        ident = {
                            "first_name": str(r.get("first_name") or "").strip(),
                            "username": "",
                        }
                        result[uid] = ident
                        _USER_IDENTITY_CACHE[uid] = {**ident, "ts": now}
        except Exception as e:
            logger.error(f"get_user_identities_batch_sync error: {e}")

    for uid in missing:
        if uid not in result:
            result[uid] = {"first_name": f"User {uid}", "username": ""}
    return result


def get_usernames_batch(user_ids: list) -> dict:
    if not user_ids:
        return {}
    result = {}
    try:
        for i in range(0, len(user_ids), 500):
            chunk = user_ids[i:i + 500]
            try:
                res = supabase.table("users").select("user_id, username, first_name").in_("user_id", chunk).execute()
                for r in res.data or []:
                    uid = int(r["user_id"])
                    uname = r.get("username")
                    fname = r.get("first_name")
                    result[uid] = (uname or fname or f"User {uid}")
            except Exception:
                res = supabase.table("users").select("user_id, first_name").in_("user_id", chunk).execute()
                for r in res.data or []:
                    uid = int(r["user_id"])
                    fname = r.get("first_name")
                    result[uid] = fname or f"User {uid}"
    except Exception as e:
        logger.error(f"get_usernames_batch error: {e}")
    return result


ADMIN_PERMISSIONS = [
    ("services", "🏷️ Services Control"),
    ("broadcast", "📢 Broadcast Control"),
    ("users", "👥 Users Control"),
    ("admins", "🛡️ Admin Control"),
    ("payouts", "💰 Manage Payouts"),
    ("live_receivers", "📡 Live Receivers"),
    ("links", "🔗 Links Control"),
    ("api", "🔌 API Control"),
    ("number_qty", "🔢 Number Quality"),
    ("extra", "⚙️ Extra Control"),
    ("withdraw_settings", "💳 Withdraw Settings"),
]

ADMIN_ROLE_PRESETS = {
    "support": {
        "label": "Support",
        "perms": ["services", "broadcast", "live_receivers"],
    },
    "payout_manager": {
        "label": "Payout Manager",
        "perms": ["payouts", "withdraw_settings"],
    },
    "super_admin": {
        "label": "Super Admin",
        "perms": [k for k, _ in ADMIN_PERMISSIONS],
    },
    "custom": {
        "label": "Custom",
        "perms": [],
    },
}


def is_admin_sync(user_id: int) -> bool:
    if user_id == ADMIN_ID:
        return True
    return user_id in ADMINS_CACHE


def get_admin_perms_record_sync(user_id: int) -> dict:
    if user_id == ADMIN_ID:
        return {
            "role": "owner",
            "perms": {k: True for k, _ in ADMIN_PERMISSIONS},
        }
    raw = get_setting(f"admin_perms:{user_id}", "")
    if raw:
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, dict):
                raw_perms = parsed.get("perms", {})
                perms = {k: bool(raw_perms.get(k, False)) for k, _ in ADMIN_PERMISSIONS}
                role = str(parsed.get("role") or "custom")
                return {"role": role, "perms": perms}
        except Exception:
            pass
    # Legacy admins without stored permission JSON default to super_admin until edited
    return {
        "role": "super_admin",
        "perms": {k: True for k, _ in ADMIN_PERMISSIONS},
    }


def set_admin_perms_sync(user_id: int, role: str, perms: dict):
    if user_id == ADMIN_ID:
        return
    clean_perms = {k: bool(perms.get(k, False)) for k, _ in ADMIN_PERMISSIONS}
    set_setting(
        f"admin_perms:{user_id}",
        json.dumps({"role": role, "perms": clean_perms}),
    )


def apply_admin_role_preset_sync(user_id: int, role_key: str):
    if user_id == ADMIN_ID or role_key not in ADMIN_ROLE_PRESETS:
        return
    if role_key == "custom":
        rec = get_admin_perms_record_sync(user_id)
        set_admin_perms_sync(user_id, "custom", rec["perms"])
        return
    preset_perms = set(ADMIN_ROLE_PRESETS[role_key]["perms"])
    perms = {k: (k in preset_perms) for k, _ in ADMIN_PERMISSIONS}
    set_admin_perms_sync(user_id, role_key, perms)


def toggle_admin_perm_sync(user_id: int, perm_key: str) -> bool:
    if user_id == ADMIN_ID:
        return True
    rec = get_admin_perms_record_sync(user_id)
    perms = dict(rec["perms"])
    new_val = not bool(perms.get(perm_key, False))
    perms[perm_key] = new_val
    set_admin_perms_sync(user_id, "custom", perms)
    return new_val


def has_admin_perm_sync(user_id: int, perm: str) -> bool:
    if not user_id:
        return False
    if user_id == ADMIN_ID:
        return True
    if not is_admin_sync(user_id):
        return False
    rec = get_admin_perms_record_sync(user_id)
    perms = rec.get("perms", {})
    if perm == "withdraw_settings":
        return bool(perms.get("withdraw_settings") or perms.get("extra"))
    return bool(perms.get(perm, False))


def has_any_global_settings_perm(user_id: int) -> bool:
    return any(
        has_admin_perm_sync(user_id, p)
        for p in ("links", "api", "number_qty", "extra", "withdraw_settings")
    )


def get_admin_role_label(user_id: int) -> str:
    if user_id == ADMIN_ID:
        return "Owner"
    rec = get_admin_perms_record_sync(user_id)
    role_key = rec.get("role", "custom")
    if role_key in ADMIN_ROLE_PRESETS:
        return ADMIN_ROLE_PRESETS[role_key]["label"]
    return "Custom"


def get_all_admins_sync() -> list:
    admins = {}
    if ADMIN_ID:
        admins[ADMIN_ID] = {"user_id": ADMIN_ID, "name": "Main Owner", "is_owner": True}
    try:
        rows = fetch_all_rows("admins", "user_id, name")
        for r in rows:
            uid_int = int(r["user_id"])
            name = str(r["name"])
            if uid_int == ADMIN_ID:
                admins[uid_int]["name"] = f"{name} (Owner)"
            else:
                admins[uid_int] = {"user_id": uid_int, "name": name, "is_owner": False}
    except Exception as e:
        logger.error(f"Supabase get admins error: {e}")
    return list(admins.values())


def add_admin_sync(user_id: int, name: str):
    ADMINS_CACHE.add(user_id)
    try:
        supabase.table("admins").upsert({"user_id": user_id, "name": name}).execute()
        if firebase_db_ref:
            firebase_db_ref.reference(f"admins/{user_id}").set({"name": name})
    except Exception as e:
        logger.error(f"Supabase add admin error: {e}")


def delete_admin_sync(user_id: int) -> bool:
    if user_id == ADMIN_ID:
        return False
    if user_id in ADMINS_CACHE:
        ADMINS_CACHE.remove(user_id)
    try:
        supabase.table("admins").delete().eq("user_id", user_id).execute()
        supabase.table("settings").delete().eq("key", f"admin_perms:{user_id}").execute()
        SETTINGS_CACHE.pop(f"admin_perms:{user_id}", None)
        if firebase_db_ref:
            firebase_db_ref.reference(f"admins/{user_id}").delete()
        return True
    except Exception as e:
        logger.error(f"Supabase delete admin error: {e}")
        return False


def _panel_row_to_dict(r: dict) -> dict:
    return {
        "id": str(r["id"]), "name": str(r["name"]), "url": str(r["url"]),
        "token": str(r["token"]),
        "polling_interval": float(r["polling_interval"]) if r.get("polling_interval") else 5.0,
        "mapping_json": r.get("mapping_json") or "",
    }


def get_all_api_panels_sync() -> list:
    try:
        try:
            rows = fetch_all_rows("api_panels", "id, name, url, token, polling_interval, mapping_json")
            if not rows:
                raise Exception("empty_or_missing")
        except Exception:
            rows = fetch_all_rows("api_panels", "id, name, url, token, polling_interval")
        return [_panel_row_to_dict(r) for r in rows]
    except Exception as e:
        logger.error(f"Supabase get API panels error: {e}")
        return []


def get_api_panel_sync(panel_id: str):
    try:
        try:
            res = supabase.table("api_panels").select("id, name, url, token, polling_interval, mapping_json").eq("id", int(panel_id)).execute()
        except Exception:
            res = supabase.table("api_panels").select("id, name, url, token, polling_interval").eq("id", int(panel_id)).execute()
        if res.data:
            return _panel_row_to_dict(res.data[0])
    except Exception as e:
        logger.error(f"Supabase get single panel error: {e}")
    return None


def _get_panel_cached_sync(panel_id: str):
    now = time.time()
    entry = _PANEL_INFO_CACHE.get(panel_id)
    if entry and (now - entry["ts"]) < PANEL_INFO_CACHE_TTL:
        return entry["data"]
    data = get_api_panel_sync(panel_id)
    _PANEL_INFO_CACHE[panel_id] = {"data": data, "ts": now}
    return data


def save_api_panel_sync(name: str, url: str, token: str,
                        polling_interval: float = 5.0,
                        mapping_json: Optional[str] = None) -> str:
    try:
        data = {
            "name": name, "url": url, "token": token,
            "polling_interval": polling_interval,
        }
        if mapping_json:
            data["mapping_json"] = mapping_json
        try:
            res = supabase.table("api_panels").insert(data).execute()
        except Exception as e:
            if "mapping_json" in str(e).lower() and "mapping_json" in data:
                data.pop("mapping_json", None)
                res = supabase.table("api_panels").insert(data).execute()
            else:
                raise
        pid = str(res.data[0]["id"])
        if firebase_db_ref:
            try:
                firebase_db_ref.reference(f"api_panels/{pid}").set(data)
            except Exception:
                pass
        _PANEL_INFO_CACHE.pop(str(pid), None)
        return pid
    except Exception as e:
        logger.error(f"Supabase save API panel error: {e}")
        return ""


def delete_api_panel_sync(panel_id: str):
    try:
        supabase.table("api_panels").delete().eq("id", int(panel_id)).execute()
        _PANEL_INFO_CACHE.pop(str(panel_id), None)
        if firebase_db_ref:
            firebase_db_ref.reference(f"api_panels/{panel_id}").delete()
    except Exception as e:
        logger.error(f"Supabase delete API panel error: {e}")

    old = CAPTCHA_SESSIONS.pop(str(panel_id), None)
    if old:
        try:
            loop = asyncio.get_event_loop()
            if loop.is_running():
                asyncio.run_coroutine_threadsafe(old["client"].aclose(), loop)
        except Exception:
            pass
    CAPTCHA_PANEL_STATUS.pop(str(panel_id), None)
    AUGESTEL_PANEL_STATUS.pop(str(panel_id), None)
    if str(panel_id) in AUGESTEL_SESSIONS:
        try:
            loop = asyncio.get_event_loop()
            if loop.is_running():
                asyncio.run_coroutine_threadsafe(_augestel_close_session(str(panel_id)), loop)
        except Exception:
            pass


def get_setting(key: str, default_val: str = "") -> str:
    if key in SETTINGS_CACHE:
        return SETTINGS_CACHE[key]
    return default_val


def set_setting(key: str, value: str):
    str_val = str(value)
    SETTINGS_CACHE[key] = str_val
    try:
        supabase.table("settings").upsert({"key": key, "value": str_val}).execute()
        if firebase_db_ref:
            firebase_db_ref.reference(f"settings/{key}").set(str_val)
    except Exception as e:
        logger.error(f"Supabase set setting error: {e}")


# ============================================================
# 🆕 COUNTRY SHORT-NAME HELPERS
# ============================================================
def get_country_short_sync(service: str, country: str) -> str:
    if not service or not country:
        return country or ""
    val = get_setting(f"country_short:{service}:{country}", "")
    return val if val else country


def set_country_short_sync(service: str, country: str, short: str):
    if not service or not country:
        return
    short = (short or "").strip()
    if not short:
        short = country
    set_setting(f"country_short:{service}:{country}", short)


def is_country_paused_sync(service: str, country: str) -> bool:
    if not service or not country:
        return False
    return str(get_setting(f"country_paused:{service}:{country}", "false")).strip().lower() == "true"


def set_country_paused_sync(service: str, country: str, paused: bool):
    if not service or not country:
        return
    set_setting(f"country_paused:{service}:{country}", "true" if paused else "false")


def get_active_countries_for_service(service: str) -> list:
    cnts = SERVICES_CACHE.get(service, {})
    return [
        c for c, avail in cnts.items()
        if avail > 0 and not is_country_paused_sync(service, c)
    ]


# ============================================================
# 🔒 FORCE JOIN HELPERS
# ============================================================
def get_force_join_chats() -> list:
    try:
        val = get_setting("force_join_chats", "[]")
        data = json.loads(val) if val else []
        return data if isinstance(data, list) else []
    except Exception:
        return []


def set_force_join_chats(chats: list):
    set_setting("force_join_chats", json.dumps(chats))


def is_force_join_enabled() -> bool:
    return get_setting("force_join_enabled", "false") == "true"


def _normalize_chat_id(raw: str):
    raw = (raw or "").strip()
    if not raw:
        return None, None
    try:
        if raw.startswith("-") or raw.isdigit():
            return int(raw), None
    except Exception:
        pass
    if raw.startswith("@"):
        return None, raw
    m = re.search(r"t\.me/([A-Za-z0-9_]+)", raw)
    if m:
        return None, "@" + m.group(1)
    if re.match(r"^[A-Za-z0-9_]+$", raw):
        return None, "@" + raw
    return None, None


async def check_user_joined_all(bot, user_id: int, chats: list) -> Tuple[bool, list]:
    missing = []
    for ch in chats:
        cid = ch.get("chat_id")
        if not cid:
            continue
        try:
            member = await bot.get_chat_member(chat_id=cid, user_id=user_id)
            if member.status in ("left", "kicked"):
                missing.append(ch)
        except Exception as e:
            logger.warning(f"force_join check error for chat {cid}: {e}")
    return (len(missing) == 0), missing


async def is_user_force_join_ok(bot, user_id: int, use_cache: bool = True) -> bool:
    if not is_force_join_enabled():
        return True
    chats = get_force_join_chats()
    if not chats:
        return True
    now = time.time()
    if use_cache:
        ts = _FORCE_JOIN_CACHE.get(user_id)
        if ts and (now - ts) < _FORCE_JOIN_CACHE_TTL:
            return True
    ok, _ = await check_user_joined_all(bot, user_id, chats)
    if ok:
        if len(_FORCE_JOIN_CACHE) >= _FORCE_JOIN_CACHE_MAX:
            _prune_ts_cache(_FORCE_JOIN_CACHE, _FORCE_JOIN_CACHE_TTL, _FORCE_JOIN_CACHE_MAX - 1, now=now)
        _FORCE_JOIN_CACHE[user_id] = now
    else:
        _FORCE_JOIN_CACHE.pop(user_id, None)
    return ok


def build_force_join_keyboard(chats: list) -> InlineKeyboardMarkup:
    buttons = []
    for ch in chats:
        link = (ch.get("link") or "").strip()
        title = ch.get("title") or "Channel"
        icon = "📢" if ch.get("type") == "channel" else "👥"
        if link:
            buttons.append([create_button(f"{icon} {title}", url=link, style="primary")])
        else:
            buttons.append([create_button(f"{icon} {title}", callback_data="noop", style="primary")])
    buttons.append([create_button("✅ I've Joined", callback_data="fj_check", style="success")])
    return InlineKeyboardMarkup(buttons)


FORCE_JOIN_TEXT = (
    "🔒 <b>JOIN REQUIRED</b>\n\n"
    "To use this bot, you must join our channel(s) and group(s) first.\n\n"
    "👇 Please join the following, then tap <b>✅ I've Joined</b>:"
)


# ============================================================
# 🎁 REFER SYSTEM HELPERS
# ============================================================
def set_user_referrer_sync(user_id: int, referrer_id: int) -> bool:
    if not user_id or not referrer_id or user_id == referrer_id:
        return False
    try:
        res = supabase.table("users").select("referred_by").eq("user_id", user_id).limit(1).execute()
        if res.data and res.data[0].get("referred_by"):
            return False
        supabase.table("users").update({"referred_by": referrer_id}).eq("user_id", user_id).execute()
        return True
    except Exception as e:
        logger.warning(f"set_user_referrer error (column missing?): {e}")
        return False


def get_user_referrer_sync(user_id: int) -> int:
    try:
        res = supabase.table("users").select("referred_by").eq("user_id", user_id).limit(1).execute()
        if res.data:
            return int(res.data[0].get("referred_by") or 0)
    except Exception as e:
        logger.warning(f"get_user_referrer error: {e}")
    return 0


def add_refer_commission_sync(referrer_id: int, amount: float) -> bool:
    if referrer_id <= 0 or amount <= 0:
        return False
    try:
        prof = get_user_profile_sync(referrer_id)
        supabase.table("users").update({
            "balance": prof["balance"] + amount,
            "refer_earned": prof["refer_earned"] + amount,
            "dirty": True,
        }).eq("user_id", referrer_id).execute()
        return True
    except Exception as e:
        logger.error(f"add_refer_commission error: {e}")
        return False


def save_user(user_id: int, first_name: str = "", username: str = ""):
    clean_fname = first_name.strip() if first_name else ""
    clean_uname = (username or "").strip().lstrip("@")
    if clean_fname or clean_uname:
        now_wall = time.time()
        if len(_USER_IDENTITY_CACHE) >= _USER_IDENTITY_CACHE_MAX and user_id not in _USER_IDENTITY_CACHE:
            _prune_identity_cache(now=now_wall)
        _USER_IDENTITY_CACHE[user_id] = {
            "first_name": clean_fname,
            "username": clean_uname,
            "ts": now_wall,
        }
    if user_id in KNOWN_USERS:
        return
    cur_date = get_bd_date_str()
    first_name = first_name.strip() if first_name else ""
    username = (username or "").strip().lstrip("@")
    try:
        existing = supabase.table("users").select("user_id").eq("user_id", user_id).limit(1).execute()
        if not existing.data:
            insert_data = {
                "user_id": user_id, "balance": 0.0, "today_earned": 0.0,
                "total_earned": 0.0, "refer_earned": 0.0, "total_otps": 0,
                "weekly_otps": 0, "first_name": first_name,
                "last_earn_date": cur_date, "dirty": True,
            }
            if username:
                insert_data["username"] = username
            try:
                supabase.table("users").insert(insert_data).execute()
            except Exception as e:
                if "username" in str(e).lower() and "column" in str(e).lower():
                    insert_data.pop("username", None)
                    supabase.table("users").insert(insert_data).execute()
                else:
                    raise
        KNOWN_USERS.add(user_id)
    except Exception as e:
        logger.error(f"Supabase save user error: {e}")


def get_user_profile_sync(user_id: int) -> dict:
    current_date = get_bd_date_str()
    try:
        res = supabase.table("users").select(
            "balance, today_earned, total_earned, refer_earned, total_otps, last_earn_date"
        ).eq("user_id", user_id).limit(1).execute()
        if res.data:
            u = res.data[0]
            bal = float(u.get("balance") or 0.0)
            today_e = float(u.get("today_earned") or 0.0)
            total_e = float(u.get("total_earned") or 0.0)
            refer_e = float(u.get("refer_earned") or 0.0)
            otps = int(u.get("total_otps") or 0)
            last_date = str(u.get("last_earn_date") or "")
            if last_date != current_date:
                today_e = 0.0
                try:
                    supabase.table("users").update({
                        "today_earned": 0.0, "last_earn_date": current_date,
                    }).eq("user_id", user_id).execute()
                except Exception:
                    pass
            return {
                "balance": bal, "today_earned": today_e, "total_earned": total_e,
                "refer_earned": refer_e, "total_otps": otps,
            }
    except Exception as e:
        logger.error(f"Supabase profile fetch error: {e}")
    return {"balance": 0.0, "today_earned": 0.0, "total_earned": 0.0, "refer_earned": 0.0, "total_otps": 0}


def get_user_hide_cc_sync(user_id: int) -> bool:
    try:
        res = supabase.table("users").select("hide_cc").eq("user_id", user_id).limit(1).execute()
        if res.data:
            return bool(res.data[0].get("hide_cc", False))
    except Exception:
        pass
    return False


def set_user_hide_cc_sync(user_id: int, hide_cc: bool):
    try:
        supabase.table("users").update({"hide_cc": hide_cc, "dirty": True}).eq("user_id", user_id).execute()
    except Exception as e:
        logger.warning(f"set_user_hide_cc_sync error: {e}")


def add_user_balance_and_otp_sync(user_id: int, amount: float = 1.0, count: int = 1) -> dict:
    current_date = get_bd_date_str()
    try:
        res = supabase.rpc("add_otp_earnings", {
            "p_user_id": user_id, "p_amount": amount,
            "p_count": count, "p_date": current_date,
        }).execute()
        if res.data:
            row = res.data[0] if isinstance(res.data, list) else res.data
            return {
                "balance": float(row.get("new_balance", 0.0)),
                "total_otps": int(row.get("new_total_otps", 0)),
            }
    except Exception as e:
        logger.error(f"Supabase add_otp_earnings RPC error: {e}")

    prof = get_user_profile_sync(user_id)
    new_bal = prof["balance"] + amount
    try:
        supabase.table("users").update({
            "balance": new_bal,
            "total_earned": prof["total_earned"] + amount,
            "today_earned": prof["today_earned"] + amount,
            "total_otps": prof["total_otps"] + count,
            "last_earn_date": current_date,
            "dirty": True,
        }).eq("user_id", user_id).execute()
    except Exception as e:
        logger.error(f"Supabase fallback earnings error: {e}")
    return {"balance": new_bal, "total_otps": prof["total_otps"] + count}


def add_otp_earnings_batch_sync(updates: list) -> dict:
    global _BATCH_RPC_AVAILABLE
    if not updates:
        return {}

    current_date = get_bd_date_str()

    if _BATCH_RPC_AVAILABLE:
        try:
            res = supabase.rpc("add_otp_earnings_batch", {
                "p_updates": updates, "p_date": current_date,
            }).execute()
            if res.data:
                result = {}
                for row in res.data:
                    result[int(row["out_user_id"])] = {
                        "balance": float(row.get("out_balance", 0.0)),
                        "total_otps": int(row.get("out_total_otps", 0)),
                    }
                return result
        except Exception as e:
            err_str = str(e)
            if ("does not exist" in err_str or "PGRST202" in err_str
                    or "Could not find" in err_str or "not find the function" in err_str):
                _BATCH_RPC_AVAILABLE = False
                logger.warning("add_otp_earnings_batch RPC not found — falling back.")
            else:
                logger.error(f"Batch earnings RPC error: {e}")

    result = {}
    for u in updates:
        try:
            r = add_user_balance_and_otp_sync(u["user_id"], u["amount"], u["count"])
        except Exception as e:
            logger.error(f"Fallback per-user earnings error for {u.get('user_id')}: {e}")
            r = {"balance": 0.0, "total_otps": 0}
        result[u["user_id"]] = r
    return result


def get_user_balance_sync(user_id: int) -> float:
    return get_user_profile_sync(user_id)["balance"]


def get_all_users() -> list:
    users = []
    try:
        rows = fetch_all_rows("users", "user_id")
        users = [int(r["user_id"]) for r in rows]
    except Exception as e:
        logger.error(f"Error fetching users from Supabase: {e}")
    return list(set(users))


def get_all_users_data_sync() -> list:
    return fetch_all_rows("users", "*")


def search_user_sync(query: str):
    try:
        q = query.strip()
        if q.isdigit():
            res = supabase.table("users").select("*").eq("user_id", int(q)).execute()
        else:
            clean_q = q.lstrip("@")
            res = supabase.table("users").select("*").eq("username", clean_q).execute()
            if not res.data:
                res = supabase.table("users").select("*").ilike("first_name", f"%{clean_q}%").execute()
        if res.data:
            return res.data[0]
    except Exception as e:
        logger.error(f"search_user_sync error: {e}")
    return None


def get_user_refer_count_sync(user_id: int) -> int:
    try:
        res = supabase.table("users").select("user_id", count="exact").eq("referred_by", user_id).execute()
        return int(res.count or 0)
    except Exception as e:
        logger.debug(f"get_user_refer_count_sync error: {e}")
    return 0


def _compute_inactive_days(user_row: dict, today_bd: Optional[datetime.date] = None) -> int:
    if today_bd is None:
        today_bd = datetime.datetime.now(_BD_TZ).date()
    raw = str(user_row.get("last_earn_date") or "").strip()
    if raw and raw != "N/A":
        try:
            d = datetime.date.fromisoformat(raw[:10])
            return max(0, (today_bd - d).days)
        except Exception:
            pass
    return 9999


_USERS_SUMMARY_COLS_CACHE: Optional[str] = None
_USERS_SUMMARY_COL_SETS = (
    "user_id, first_name, username, balance, total_otps, weekly_otps, last_earn_date, is_banned, created_at",
    "user_id, first_name, username, balance, total_otps, weekly_otps, last_earn_date, is_banned",
    "user_id, first_name, balance, total_otps, weekly_otps, last_earn_date",
)


def _fetch_users_summary_rows_sync(filters: Optional[dict] = None) -> list:
    global _USERS_SUMMARY_COLS_CACHE
    candidates = (
        [_USERS_SUMMARY_COLS_CACHE] + [c for c in _USERS_SUMMARY_COL_SETS if c != _USERS_SUMMARY_COLS_CACHE]
        if _USERS_SUMMARY_COLS_CACHE else list(_USERS_SUMMARY_COL_SETS)
    )
    for cols in candidates:
        if filters and "is_banned" in filters and "is_banned" not in cols:
            continue
        try:
            all_rows = []
            offset = 0
            while True:
                q = supabase.table("users").select(cols)
                if filters:
                    for k, v in filters.items():
                        q = q.eq(k, v)
                r = q.range(offset, offset + SUPABASE_PAGE_SIZE - 1).execute()
                if not r.data:
                    break
                all_rows.extend(r.data)
                if len(r.data) < SUPABASE_PAGE_SIZE:
                    break
                offset += SUPABASE_PAGE_SIZE
            _USERS_SUMMARY_COLS_CACHE = cols
            return all_rows
        except Exception as e:
            err_l = str(e).lower()
            if "column" in err_l or "does not exist" in err_l or "pgrst" in err_l:
                continue
            logger.error(f"_fetch_users_summary_rows_sync error: {e}")
            return []
    return []


def get_users_ordered_sync(sort_mode: str = "recent") -> list:
    rows = _fetch_users_summary_rows_sync()
    if not rows:
        return []
    has_ts = any(r.get("created_at") for r in rows)
    has_id = any(r.get("id") is not None for r in rows)
    reverse = (sort_mode != "old")
    if has_ts or has_id:
        return sorted(
            rows,
            key=lambda r: (str(r.get("created_at") or ""), int(r.get("id") or 0), int(r.get("user_id") or 0)),
            reverse=reverse,
        )
    return list(reversed(rows)) if reverse else list(rows)


def get_banned_users_list_sync() -> list:
    rows = _fetch_users_summary_rows_sync(filters={"is_banned": True})
    seen_uids = {int(r.get("user_id") or 0) for r in rows if r.get("user_id")}
    missing_mem = [uid for uid in _IN_MEMORY_BANNED if uid and uid not in seen_uids]
    if missing_mem:
        cols = _USERS_SUMMARY_COLS_CACHE or _USERS_SUMMARY_COL_SETS[-1]
        for i in range(0, len(missing_mem), 200):
            chunk = missing_mem[i:i + 200]
            try:
                r = supabase.table("users").select(cols).in_("user_id", chunk).execute()
                for row in r.data or []:
                    rows.append(row)
                    seen_uids.add(int(row.get("user_id") or 0))
            except Exception:
                pass
        for uid in missing_mem:
            if uid not in seen_uids:
                rows.append({"user_id": uid, "first_name": f"User {uid}", "balance": 0.0, "is_banned": True})
    if not rows and _IN_MEMORY_BANNED:
        rows = [{"user_id": uid, "first_name": f"User {uid}", "balance": 0.0, "is_banned": True} for uid in _IN_MEMORY_BANNED]
    has_ts = any(r.get("created_at") for r in rows)
    if has_ts:
        rows.sort(key=lambda r: (str(r.get("created_at") or ""), int(r.get("user_id") or 0)), reverse=True)
    else:
        rows.reverse()
    return rows


def get_inactive_users_list_sync(window: str = "7d") -> list:
    win_days = {"24h": 1, "3d": 3, "7d": 7, "15d": 15, "30d": 30}.get(window, 7)
    rows = _fetch_users_summary_rows_sync()
    today_bd = datetime.datetime.now(_BD_TZ).date()
    result = []
    for r in rows:
        uid = int(r.get("user_id") or 0)
        if not uid or is_admin_sync(uid):
            continue
        days = _compute_inactive_days(r, today_bd)
        weekly = int(r.get("weekly_otps") or 0)
        total_o = int(r.get("total_otps") or 0)
        if days >= win_days or total_o == 0 or weekly < 10:
            item = dict(r)
            item["_inactive_days"] = days
            result.append(item)
    result.sort(key=lambda r: (-r["_inactive_days"], int(r.get("weekly_otps") or 0), int(r.get("total_otps") or 0)))
    return result


def run_inactive_autoban_sweep_sync() -> list:
    if not is_inactive_autoban_enabled():
        return []
    min_days = get_inactive_autoban_days()
    min_otps = get_inactive_autoban_min_otps()
    rows = _fetch_users_summary_rows_sync()
    today_bd = datetime.datetime.now(_BD_TZ).date()
    banned_list = []
    for r in rows:
        uid = int(r.get("user_id") or 0)
        if not uid or is_admin_sync(uid):
            continue
        if bool(r.get("is_banned")) or (uid in _IN_MEMORY_BANNED):
            continue
        days = _compute_inactive_days(r, today_bd)
        weekly = int(r.get("weekly_otps") or 0)
        if days >= min_days and weekly < min_otps:
            reason = f"Auto-ban: Inactive {days}d & {weekly} weekly OTPs"
            set_user_banned_sync(uid, True, reason)
            banned_list.append({
                "uid": uid,
                "name": str(r.get("first_name") or r.get("username") or f"User {uid}"),
                "days": days,
                "weekly": weekly,
                "reason": reason,
            })
    return banned_list


def get_global_stats_sync():
    try:
        rows = fetch_all_rows("users", "balance, total_earned, today_earned, refer_earned, total_otps, weekly_otps")

        total_balance = sum(float(r.get("balance") or 0.0) for r in rows)
        total_earned = sum(float(r.get("total_earned") or 0.0) for r in rows)
        total_today = sum(float(r.get("today_earned") or 0.0) for r in rows)
        total_refer = sum(float(r.get("refer_earned") or 0.0) for r in rows)
        total_otps = sum(int(r.get("total_otps") or 0) for r in rows)
        total_weekly_otps = sum(int(r.get("weekly_otps") or 0) for r in rows)

        return {
            "total_users": len(rows),
            "total_balance": total_balance,
            "total_earned": total_earned,
            "total_today": total_today,
            "total_refer": total_refer,
            "total_otps": total_otps,
            "total_weekly_otps": total_weekly_otps
        }
    except Exception as e:
        logger.error(f"get_global_stats_sync error: {e}")
        return {}


def check_and_process_weekly_reset_sync() -> list:
    current_friday = get_current_friday_str()
    last_reset = get_setting("last_weekly_reset_friday", "")
    if not last_reset:
        set_setting("last_weekly_reset_friday", current_friday)
        return []
    if last_reset == current_friday:
        return []

    is_bonus_enabled = get_setting("ranking_bonus_enabled", "true") == "true"
    top_users = []
    try:
        res = supabase.table("users").select("user_id, weekly_otps, total_otps").gt("weekly_otps", 0).order(
            "weekly_otps", desc=True).order("total_otps", desc=True).limit(3).execute()
        top_users = res.data
    except Exception as e:
        logger.error(f"Supabase fetch top ranking error: {e}")

    notifications = []
    if is_bonus_enabled and top_users:
        for rank_idx, u in enumerate(top_users, start=1):
            uid = u["user_id"]
            b_str = get_setting(f"rank_bonus_{rank_idx}", "0")
            try:
                b_amt = float(b_str)
            except (ValueError, TypeError):
                b_amt = 0.0
            if b_amt > 0:
                refund_user_balance_sync(uid, b_amt)
                notifications.append({"uid": uid, "amount": b_amt, "rank": rank_idx})

    try:
        supabase.table("users").update({"weekly_otps": 0, "dirty": True}).gt("weekly_otps", 0).execute()
    except Exception as e:
        logger.error(f"Supabase reset weekly otps error: {e}")

    set_setting("last_weekly_reset_friday", current_friday)
    return notifications


def get_ranking_leaderboard_sync(user_id: int) -> str:
    now = time.time()
    top_5 = None
    if LEADERBOARD_CACHE["data"] is not None and now - LEADERBOARD_CACHE["ts"] < LEADERBOARD_CACHE_TTL:
        top_5 = LEADERBOARD_CACHE["data"]
    else:
        try:
            res = supabase.table("users").select("user_id, first_name, weekly_otps, total_otps").gt("weekly_otps", 0).order(
                "weekly_otps", desc=True).order("total_otps", desc=True).limit(5).execute()
            top_5 = res.data
            LEADERBOARD_CACHE["data"] = top_5
            LEADERBOARD_CACHE["ts"] = now
        except Exception as e:
            logger.error(f"Supabase leaderboard fetch error: {e}")
            top_5 = []

    user_rank = "N/A"
    user_weekly_otps = 0
    try:
        res = supabase.table("users").select("weekly_otps").eq("user_id", user_id).limit(1).execute()
        if res.data:
            user_weekly_otps = int(res.data[0].get("weekly_otps") or 0)
        if user_weekly_otps > 0:
            hr = supabase.table("users").select("user_id", count="exact").gt("weekly_otps", user_weekly_otps).execute()
            higher_cnt = hr.count if hr.count else 0
            user_rank = f"#{higher_cnt + 1}"
    except Exception as e:
        logger.error(f"Supabase user rank error: {e}")

    viewer_is_admin = is_admin_sync(user_id)

    medals = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣"]
    text = "🏆 <b>WEEKLY TOP OTP RECEIVERS</b>\n━━━━━━━━━━━━━━━━━━━━\n"
    if top_5:
        for idx, u in enumerate(top_5):
            uid = u["user_id"]
            fname = u.get("first_name") or f"User {uid}"
            w_otps = u.get("weekly_otps", 0)
            medal = medals[idx] if idx < len(medals) else f"{idx+1}."
            safe_fname = html.escape(fname)
            if viewer_is_admin:
                user_link = f'<a href="tg://user?id={uid}">{safe_fname}</a>'
            else:
                user_link = safe_fname
            text += f"{medal} {user_link} — <b>{w_otps}</b> OTPs\n"
    else:
        text += "<i>No OTP receivers this week yet. Be the first!</i>\n"
    text += "━━━━━━━━━━━━━━━━━━━━\n"
    text += f"👤 <b>Your Rank:</b> {user_rank} ({user_weekly_otps} OTPs)"
    return text


def push_dirty_to_firebase_sync() -> int:
    if not firebase_db_ref:
        return 0
    total_pushed = 0
    try:
        while True:
            res = supabase.table("users").select(
                "user_id, balance, today_earned, total_earned, total_otps, weekly_otps, last_earn_date, first_name"
            ).eq("dirty", True).limit(FIREBASE_BACKUP_BATCH_SIZE).execute()
            rows = res.data
            if not rows:
                break
            updates = {}
            user_ids = []
            for u in rows:
                uid = u["user_id"]
                updates[f"users/{uid}/balance"] = float(u.get("balance") or 0.0)
                updates[f"users/{uid}/today_earned"] = float(u.get("today_earned") or 0.0)
                updates[f"users/{uid}/total_earned"] = float(u.get("total_earned") or 0.0)
                updates[f"users/{uid}/total_otps"] = int(u.get("total_otps") or 0)
                updates[f"users/{uid}/weekly_otps"] = int(u.get("weekly_otps") or 0)
                updates[f"users/{uid}/last_earn_date"] = str(u.get("last_earn_date") or "")
                updates[f"users/{uid}/exists"] = True
                fn = u.get("first_name") or ""
                if fn:
                    updates[f"users/{uid}/first_name"] = fn
                user_ids.append(uid)
            if updates:
                firebase_db_ref.reference("/").update(updates)
                try:
                    supabase.table("users").update({"dirty": False}).in_("user_id", user_ids).execute()
                except Exception as e:
                    logger.error(f"clear dirty error: {e}")
                total_pushed += len(user_ids)
            if len(rows) < FIREBASE_BACKUP_BATCH_SIZE:
                break
        if total_pushed:
            logger.info(f"Firebase backup: pushed {total_pushed} dirty users")
    except Exception as e:
        logger.error(f"push_dirty_to_firebase_sync error: {e}")
    return total_pushed


async def firebase_backup_worker():
    await asyncio.sleep(30)
    try:
        await asyncio.to_thread(push_dirty_to_firebase_sync)
    except Exception as e:
        logger.error(f"Initial Firebase backup error: {e}")

    while True:
        await asyncio.sleep(FIREBASE_BACKUP_INTERVAL)
        try:
            await asyncio.to_thread(push_dirty_to_firebase_sync)
        except Exception as e:
            logger.error(f"Firebase backup worker error: {e}")


def restore_from_firebase_to_supabase():
    if not firebase_db_ref:
        return
    try:
        res = supabase.table("users").select("user_id", count="exact").limit(1).execute()
        if res.count and res.count > 0:
            logger.info("Supabase has data — skipping Firebase restore")
            return
        logger.info("Supabase empty — restoring from Firebase...")

        fb_users = firebase_db_ref.reference("users").get()
        if fb_users and isinstance(fb_users, dict):
            batch = []
            for uid, u in fb_users.items():
                if not str(uid).isdigit():
                    continue
                batch.append({
                    "user_id": int(uid),
                    "balance": float(u.get("balance") or 0.0),
                    "today_earned": float(u.get("today_earned") or 0.0),
                    "total_earned": float(u.get("total_earned") or 0.0),
                    "refer_earned": float(u.get("refer_earned") or 0.0),
                    "total_otps": int(u.get("total_otps") or 0),
                    "weekly_otps": int(u.get("weekly_otps") or 0),
                    "first_name": str(u.get("first_name") or ""),
                    "last_earn_date": str(u.get("last_earn_date") or ""),
                    "dirty": False,
                })
            for i in range(0, len(batch), 500):
                try:
                    supabase.table("users").upsert(batch[i:i+500]).execute()
                except Exception as e:
                    logger.error(f"restore users error: {e}")

        fb_settings = firebase_db_ref.reference("settings").get()
        if fb_settings and isinstance(fb_settings, dict):
            rows = [{"key": str(k), "value": str(v)} for k, v in fb_settings.items() if v is not None]
            if rows:
                try:
                    supabase.table("settings").upsert(rows).execute()
                except Exception as e:
                    logger.error(f"restore settings error: {e}")

        fb_payouts = firebase_db_ref.reference("payouts").get()
        if fb_payouts and isinstance(fb_payouts, dict):
            rows = []
            for srv, cnts in fb_payouts.items():
                if isinstance(cnts, dict):
                    for cnt, val in cnts.items():
                        rows.append({"service_name": srv, "country_name": cnt, "payout": float(val)})
            if rows:
                try:
                    supabase.table("payouts").upsert(rows).execute()
                except Exception as e:
                    logger.error(f"restore payouts error: {e}")

        fb_admins = firebase_db_ref.reference("admins").get()
        if fb_admins and isinstance(fb_admins, dict):
            rows = []
            for uid, adata in fb_admins.items():
                if str(uid).isdigit():
                    name = adata.get("name", "Admin") if isinstance(adata, dict) else "Admin"
                    rows.append({"user_id": int(uid), "name": str(name)})
            if rows:
                try:
                    supabase.table("admins").upsert(rows).execute()
                except Exception as e:
                    logger.error(f"restore admins error: {e}")

        fb_methods = firebase_db_ref.reference("withdraw_methods").get()
        if fb_methods and isinstance(fb_methods, dict):
            rows = [{"name": str(m)} for m in fb_methods.keys()]
            if rows:
                try:
                    supabase.table("withdraw_methods").upsert(rows).execute()
                except Exception:
                    pass

        logger.info("Firebase → Supabase restore complete")
    except Exception as e:
        logger.error(f"Restore from Firebase error: {e}")


def load_known_users():
    try:
        res = supabase.table("users").select("user_id").limit(MAX_KNOWN_USERS).execute()
        for r in res.data:
            KNOWN_USERS.add(int(r["user_id"]))
        logger.info(f"Loaded {len(KNOWN_USERS)} known users")
    except Exception as e:
        logger.error(f"load_known_users error: {e}")


def refresh_all_caches_sync():
    global SETTINGS_CACHE, ADMINS_CACHE
    SETTINGS_CACHE.clear()
    ADMINS_CACHE.clear()

    if ADMIN_ID:
        ADMINS_CACHE.add(ADMIN_ID)

    try:
        rows = fetch_all_rows("settings", "key, value")
        for r in rows:
            SETTINGS_CACHE[str(r["key"])] = str(r["value"])
    except Exception as e:
        logger.error(f"Error loading settings: {e}")

    try:
        rows = fetch_all_rows("admins", "user_id")
        for r in rows:
            ADMINS_CACHE.add(int(r["user_id"]))
    except Exception as e:
        logger.error(f"Error loading admins: {e}")

    refresh_services_cache_sync()
    refresh_payouts_cache_sync()


def refresh_services_cache_sync():
    global SERVICES_CACHE
    new_cache = {}
    try:
        srv_rows = fetch_all_rows("services", "service_name, country_name")
        for r in srv_rows:
            new_cache.setdefault(r["service_name"], {})[r["country_name"]] = 0

        allocated = set()
        try:
            alloc_rows = fetch_all_rows("allocations", "number")
            allocated = {str(a["number"]) for a in alloc_rows}
        except Exception as e:
            logger.error(f"allocations read error: {e}")

        for srv, cnts in new_cache.items():
            for cnt in list(cnts.keys()):
                try:
                    num_rows = fetch_all_rows(
                        "numbers", "number",
                        filters={"service": srv, "country": cnt, "status": "available"},
                    )
                    new_cache[srv][cnt] = sum(
                        1 for n in num_rows if str(n["number"]) not in allocated
                    )
                except Exception as e:
                    logger.error(f"count error for {srv}/{cnt}: {e}")
    except Exception as e:
        logger.error(f"Error populating services cache: {e}")
    SERVICES_CACHE = new_cache
    for srv, cnts in SERVICES_CACHE.items():
        for cnt, count in cnts.items():
            if count <= 0 and not is_country_paused_sync(srv, cnt):
                set_country_paused_sync(srv, cnt, True)


def get_admin_services_summary():
    return SERVICES_CACHE


def _delete_setting_key_sync(key: str):
    SETTINGS_CACHE.pop(key, None)
    try:
        supabase.table("settings").delete().eq("key", key).execute()
    except Exception as e:
        logger.warning(f"delete setting {key} error: {e}")
    if firebase_db_ref:
        try:
            firebase_db_ref.reference(f"settings/{key}").delete()
        except Exception:
            pass


def delete_service_db(service: str):
    cnts = list(SERVICES_CACHE.get(service, {}).keys())
    try:
        supabase.table("services").delete().eq("service_name", service).execute()
        supabase.table("numbers").delete().eq("service", service).execute()
        supabase.table("payouts").delete().eq("service_name", service).execute()
    except Exception as e:
        logger.error(f"Supabase delete service error: {e}")
    for cnt in cnts:
        _delete_setting_key_sync(f"country_short:{service}:{cnt}")
        _delete_setting_key_sync(f"cc_len:{service}:{cnt}")
        _delete_setting_key_sync(f"country_paused:{service}:{cnt}")
    if firebase_db_ref:
        try:
            firebase_db_ref.reference(f"services/{service}").delete()
            firebase_db_ref.reference(f"numbers/{service}").delete()
            firebase_db_ref.reference(f"payouts/{service}").delete()
        except Exception as e:
            logger.error(f"Firebase delete service error: {e}")
    refresh_services_cache_sync()
    refresh_payouts_cache_sync()


def delete_country_db(service: str, country: str):
    try:
        supabase.table("services").delete().eq("service_name", service).eq("country_name", country).execute()
        supabase.table("numbers").delete().eq("service", service).eq("country", country).execute()
        supabase.table("payouts").delete().eq("service_name", service).eq("country_name", country).execute()
    except Exception as e:
        logger.error(f"Supabase delete country error: {e}")
    _delete_setting_key_sync(f"country_short:{service}:{country}")
    _delete_setting_key_sync(f"cc_len:{service}:{country}")
    _delete_setting_key_sync(f"country_paused:{service}:{country}")
    if firebase_db_ref:
        try:
            firebase_db_ref.reference(f"services/{service}/{country}").delete()
            firebase_db_ref.reference(f"numbers/{service}/{country}").delete()
            firebase_db_ref.reference(f"payouts/{service}/{country}").delete()
        except Exception as e:
            logger.error(f"Firebase delete country error: {e}")
    refresh_services_cache_sync()
    refresh_payouts_cache_sync()


def clear_country_stock_db(service: str, country: str) -> int:
    cleared = 0
    to_delete = []
    try:
        num_rows = fetch_all_rows(
            "numbers", "number",
            filters={"service": service, "country": country, "status": "available"},
        )
        candidates = [str(r["number"]) for r in num_rows if r.get("number")]
        allocated_set = set()
        for i in range(0, len(candidates), 500):
            chunk = candidates[i:i + 500]
            try:
                alloc_rows = (
                    supabase.table("allocations")
                    .select("number")
                    .in_("number", chunk)
                    .execute().data or []
                )
                for r in alloc_rows:
                    allocated_set.add(str(r["number"]))
            except Exception as e:
                logger.error(f"clear_country_stock_db alloc check error: {e}")

        to_delete = [n for n in candidates if n not in allocated_set]
        for i in range(0, len(to_delete), 500):
            chunk = to_delete[i:i + 500]
            try:
                (
                    supabase.table("numbers")
                    .delete()
                    .eq("service", service)
                    .eq("country", country)
                    .eq("status", "available")
                    .in_("number", chunk)
                    .execute()
                )
                cleared += len(chunk)
            except Exception as e:
                logger.error(f"clear_country_stock_db delete chunk error: {e}")
    except Exception as e:
        logger.error(f"Supabase clear_country_stock_db error: {e}")

    if firebase_db_ref and to_delete:
        try:
            for i in range(0, len(to_delete), 500):
                chunk = to_delete[i:i + 500]
                firebase_db_ref.reference(f"numbers/{service}/{country}").update({n: None for n in chunk})
        except Exception as e:
            logger.warning(f"Firebase clear_country_stock_db error: {e}")

    if service in SERVICES_CACHE and country in SERVICES_CACHE[service]:
        SERVICES_CACHE[service][country] = 0
    set_country_paused_sync(service, country, True)
    return cleared


def rename_service_db(old_service: str, new_service: str) -> Tuple[bool, str]:
    old_service = (old_service or "").strip()
    new_service = (new_service or "").strip()
    if not old_service or not new_service:
        return False, "Service name cannot be empty."
    if old_service == new_service:
        return True, "No change."
    if new_service in SERVICES_CACHE:
        return False, f"Service '{_cb_clean(new_service)}' already exists."

    cnts = list(SERVICES_CACHE.get(old_service, {}).keys())
    try:
        supabase.table("services").update({"service_name": new_service}).eq("service_name", old_service).execute()
        supabase.table("numbers").update({"service": new_service}).eq("service", old_service).execute()
        supabase.table("payouts").update({"service_name": new_service}).eq("service_name", old_service).execute()
        supabase.table("allocations").update({"service": new_service}).eq("service", old_service).execute()
    except Exception as e:
        logger.error(f"Supabase rename_service_db error: {e}")
        return False, f"Database error: {e}"

    for cnt in cnts:
        old_short_key = f"country_short:{old_service}:{cnt}"
        if old_short_key in SETTINGS_CACHE:
            set_setting(f"country_short:{new_service}:{cnt}", SETTINGS_CACHE[old_short_key])
            _delete_setting_key_sync(old_short_key)
        old_cc_key = f"cc_len:{old_service}:{cnt}"
        if old_cc_key in SETTINGS_CACHE:
            set_setting(f"cc_len:{new_service}:{cnt}", SETTINGS_CACHE[old_cc_key])
            _delete_setting_key_sync(old_cc_key)
        old_pause_key = f"country_paused:{old_service}:{cnt}"
        if old_pause_key in SETTINGS_CACHE:
            set_setting(f"country_paused:{new_service}:{cnt}", SETTINGS_CACHE[old_pause_key])
            _delete_setting_key_sync(old_pause_key)

    if firebase_db_ref:
        try:
            for root in ("services", "numbers", "payouts"):
                val = firebase_db_ref.reference(f"{root}/{old_service}").get()
                if val is not None:
                    firebase_db_ref.reference(f"{root}/{new_service}").set(val)
                    firebase_db_ref.reference(f"{root}/{old_service}").delete()
        except Exception as e:
            logger.warning(f"Firebase rename_service_db error: {e}")

    refresh_services_cache_sync()
    refresh_payouts_cache_sync()
    return True, "Renamed"


def rename_country_db(service: str, old_country: str, new_country: str) -> Tuple[bool, str]:
    service = (service or "").strip()
    old_country = (old_country or "").strip()
    new_country = (new_country or "").strip()
    if not service or not old_country or not new_country:
        return False, "Country name cannot be empty."
    if old_country == new_country:
        return True, "No change."
    if new_country in SERVICES_CACHE.get(service, {}):
        return False, f"Country '{_cb_clean(new_country)}' already exists in this service."

    try:
        supabase.table("services").update({"country_name": new_country}).eq("service_name", service).eq("country_name", old_country).execute()
        supabase.table("numbers").update({"country": new_country}).eq("service", service).eq("country", old_country).execute()
        supabase.table("payouts").update({"country_name": new_country}).eq("service_name", service).eq("country_name", old_country).execute()
        supabase.table("allocations").update({"country": new_country}).eq("service", service).eq("country", old_country).execute()
    except Exception as e:
        logger.error(f"Supabase rename_country_db error: {e}")
        return False, f"Database error: {e}"

    old_short_key = f"country_short:{service}:{old_country}"
    if old_short_key in SETTINGS_CACHE:
        set_setting(f"country_short:{service}:{new_country}", SETTINGS_CACHE[old_short_key])
        _delete_setting_key_sync(old_short_key)
    old_cc_key = f"cc_len:{service}:{old_country}"
    if old_cc_key in SETTINGS_CACHE:
        set_setting(f"cc_len:{service}:{new_country}", SETTINGS_CACHE[old_cc_key])
        _delete_setting_key_sync(old_cc_key)
    old_pause_key = f"country_paused:{service}:{old_country}"
    if old_pause_key in SETTINGS_CACHE:
        set_setting(f"country_paused:{service}:{new_country}", SETTINGS_CACHE[old_pause_key])
        _delete_setting_key_sync(old_pause_key)

    if firebase_db_ref:
        try:
            for root in ("services", "numbers", "payouts"):
                val = firebase_db_ref.reference(f"{root}/{service}/{old_country}").get()
                if val is not None:
                    firebase_db_ref.reference(f"{root}/{service}/{new_country}").set(val)
                    firebase_db_ref.reference(f"{root}/{service}/{old_country}").delete()
        except Exception as e:
            logger.warning(f"Firebase rename_country_db error: {e}")

    refresh_services_cache_sync()
    refresh_payouts_cache_sync()
    return True, "Renamed"


def get_countries_for_service(service: str) -> list:
    if service in SERVICES_CACHE:
        return list(SERVICES_CACHE[service].keys())
    return []


def save_numbers_sync(service: str, country: str, numbers: list, payout: float = None) -> int:
    cleaned_numbers = []
    seen = set()
    for num in numbers:
        clean_num = re.sub(r'\D', '', str(num))
        if clean_num and clean_num not in seen:
            seen.add(clean_num)
            cleaned_numbers.append(clean_num)

    if not cleaned_numbers:
        return 0

    inserted = 0
    to_insert = []
    try:
        supabase.table("services").upsert({
            "service_name": service, "country_name": country,
        }).execute()

        existing = set()
        try:
            num_rows = fetch_all_rows(
                "numbers", "number",
                filters={"service": service, "country": country},
            )
            existing = {str(r["number"]) for r in num_rows}
        except Exception as e:
            logger.error(f"existing numbers read error: {e}")

        candidates = [n for n in cleaned_numbers if n not in existing]

        globally_used = set()
        for i in range(0, len(candidates), 500):
            chunk = candidates[i:i + 500]
            try:
                alloc_rows = (supabase.table("allocations")
                              .select("number")
                              .in_("number", chunk)
                              .execute().data or [])
                for r in alloc_rows:
                    globally_used.add(str(r["number"]))
            except Exception as e:
                logger.error(f"chunk alloc check error: {e}")

        to_insert = [n for n in candidates if n not in globally_used]

        for i in range(0, len(to_insert), 500):
            chunk = to_insert[i:i + 500]
            try:
                supabase.table("numbers").insert([
                    {"service": service, "country": country, "number": n,
                     "status": "available", "user_id": 0}
                    for n in chunk
                ]).execute()
                inserted += len(chunk)
            except Exception as e:
                logger.error(f"batch numbers insert error: {e}")
    except Exception as e:
        logger.error(f"save_numbers error: {e}")

    if payout is not None:
        set_payout_sync(service, country, payout)

    if firebase_db_ref and inserted > 0:
        try:
            updates = {}
            for n in to_insert[:2000]:
                updates[f"numbers/{service}/{country}/{n}"] = {
                    "number": n, "status": "available", "user_id": 0
                }
            if updates:
                firebase_db_ref.reference("/").update(updates)
            firebase_db_ref.reference(f"services/{service}/{country}").set(True)
        except Exception as e:
            logger.error(f"Firebase mirror numbers error: {e}")

    try:
        if service not in SERVICES_CACHE:
            SERVICES_CACHE[service] = {}
        if country not in SERVICES_CACHE[service]:
            SERVICES_CACHE[service][country] = 0
        SERVICES_CACHE[service][country] += inserted
        if SERVICES_CACHE[service][country] <= 0:
            set_country_paused_sync(service, country, True)
    except Exception as e:
        logger.warning(f"incremental cache update failed: {e}")

    return inserted


def allocate_numbers_sync(service: str, country: str, user_id: int, target_qty: int, exclude: list = None) -> list:
    exclude_list = [str(x) for x in (exclude or [])]
    target_qty = max(1, int(target_qty))

    try:
        res = supabase.rpc("allocate_numbers_batch", {
            "p_service": service,
            "p_country": country,
            "p_user_id": user_id,
            "p_qty": target_qty,
            "p_exclude": exclude_list
        }).execute()

        assigned = res.data if res.data else []

        if service in SERVICES_CACHE and country in SERVICES_CACHE[service]:
            SERVICES_CACHE[service][country] = max(0, SERVICES_CACHE[service][country] - len(assigned))
            if SERVICES_CACHE[service][country] <= 0:
                set_country_paused_sync(service, country, True)

        if firebase_db_ref and assigned:
            try:
                updates = {}
                for n in assigned:
                    updates[f"allocations/{n}"] = {
                        "user_id": user_id, "service": service, "country": country,
                        "allocated_at": int(time.time()),
                    }
                    updates[f"numbers/{service}/{country}/{n}/status"] = "allocated"
                    updates[f"numbers/{service}/{country}/{n}/user_id"] = user_id
                firebase_db_ref.reference("/").update(updates)
            except Exception as e:
                logger.error(f"Firebase mirror alloc error: {e}")

        return [str(n) for n in assigned]

    except Exception as e:
        logger.error(f"allocate batch RPC error: {e}")
        return []


def get_user_allocations_sync(user_id: int, service: str, country: str) -> list:
    try:
        rows = fetch_all_rows(
            "allocations", "number",
            filters={"user_id": user_id, "service": service, "country": country},
        )
        return [str(r["number"]) for r in rows]
    except Exception as e:
        logger.error(f"Supabase get user allocations error: {e}")
        return []


def load_seen_otp_ids_sync() -> dict:
    cutoff = int(time.time()) - OTP_ID_RETENTION_SECONDS
    result = {}
    try:
        offset = 0
        while len(result) < PROCESSED_IDS_MAX:
            remaining = PROCESSED_IDS_MAX - len(result)
            batch_limit = min(SUPABASE_PAGE_SIZE, remaining)
            r = (supabase.table("seen_otps")
                 .select("msg_id, ts")
                 .gte("ts", cutoff)
                 .order("ts", desc=True)
                 .range(offset, offset + batch_limit - 1)
                 .execute())
            if not r.data:
                break
            for row in r.data:
                result[row["msg_id"]] = row.get("ts", 0)
            if len(r.data) < batch_limit:
                break
            offset += batch_limit
    except Exception as e:
        logger.error(f"Supabase load seen otps error: {e}")
    return result


def mark_otp_seen_batch_sync(msg_ids: list):
    if not msg_ids:
        return
    ts = int(time.time())
    try:
        supabase.table("seen_otps").upsert([{"msg_id": m, "ts": ts} for m in msg_ids]).execute()
    except Exception as e:
        logger.error(f"Supabase batch mark otp seen error: {e}")
        raise


def cleanup_old_otp_ids_sync():
    cutoff = int(time.time()) - OTP_ID_RETENTION_SECONDS
    try:
        supabase.table("seen_otps").delete().lt("ts", cutoff).execute()
    except Exception as e:
        logger.error(f"Supabase cleanup seen otps error: {e}")


def build_admin_control_view(use_premium: Optional[bool] = None):
    admins = get_all_admins_sync()
    text = (
        "🛠 **ADMIN CONTROL MANAGEMENT**\n\n"
        f"Total Admins: `{len(admins)}`\n"
        "Select an admin below to view/manage permissions or add a new admin."
    )
    buttons = []

    for adm in admins:
        uid = adm["user_id"]
        name = adm["name"]
        is_owner = adm.get("is_owner", False) or (uid == ADMIN_ID)
        if is_owner:
            label = f"👑 {name} [Owner]"
            style = "primary"
            emoji_id = "5258508428212445001"
            fallback_e = "👑"
        else:
            role_lbl = get_admin_role_label(uid)
            label = f"{name} [{role_lbl}]"
            style = "primary"
            emoji_id = "5258508428212445001"
            fallback_e = "🛡️"
        buttons.append([_admin_inline_btn(
            label, callback_data=f"adm:ctrl:view:{uid}",
            style=style, emoji_id=emoji_id,
            fallback_emoji=fallback_e, use_premium=use_premium,
        )])

    buttons.append([_admin_inline_btn(
        "Add New Admin", callback_data="adm:add:start",
        style="success", emoji_id="5287354223141342798",
        fallback_emoji="➕", use_premium=use_premium,
    )])
    buttons.append([
        _admin_inline_btn(
            "Back to User Manager", callback_data="adm:usr:manager",
            style="danger", emoji_id="5456187398977247949",
            fallback_emoji="◀️", use_premium=use_premium,
        ),
    ])
    return text, InlineKeyboardMarkup(buttons)


def build_admin_detail_view(target_uid: int, use_premium: Optional[bool] = None):
    admins = get_all_admins_sync()
    target_adm = next((a for a in admins if a["user_id"] == target_uid), None)
    name = target_adm["name"] if target_adm else f"Admin {target_uid}"
    is_owner = (target_uid == ADMIN_ID) or (target_adm and target_adm.get("is_owner", False))

    if is_owner:
        text = (
            "👑 **MAIN OWNER PROFILE**\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            f"👤 **Name:** `{escape_md(name)}`\n"
            f"🆔 **User ID:** `{target_uid}`\n"
            f"🛡️ **Role:** `Main Owner (All Permissions)`\n\n"
            "🔒 _Main Owner permissions cannot be restricted and the Owner cannot be removed._"
        )
        buttons = [[
            _admin_inline_btn(
                "Back", callback_data="adm:ctrl:list",
                style="danger", emoji_id="5456187398977247949",
                fallback_emoji="◀️", use_premium=use_premium,
            )
        ]]
        return text, InlineKeyboardMarkup(buttons)

    rec = get_admin_perms_record_sync(target_uid)
    role_key = rec.get("role", "custom")
    role_label = ADMIN_ROLE_PRESETS.get(role_key, {}).get("label", "Custom")
    perms = rec.get("perms", {})
    enabled_cnt = sum(1 for k, _ in ADMIN_PERMISSIONS if perms.get(k, False))

    text = (
        "🛡️ **ADMIN PERMISSIONS**\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 **Name:** `{escape_md(name)}`\n"
        f"🆔 **User ID:** `{target_uid}`\n"
        f"🎭 **Role Preset:** `{role_label}`\n"
        f"🔑 **Enabled Rights:** `{enabled_cnt}/{len(ADMIN_PERMISSIONS)}`\n\n"
        "Select a quick preset or toggle individual permissions below:"
    )

    buttons = [
        [
            create_button(
                f"{'• Support •' if role_key == 'support' else 'Support'}",
                callback_data=f"adm:ctrl:preset:{target_uid}:support",
                style="success" if role_key == "support" else "primary",
            ),
            create_button(
                f"{'• Payout Mgr •' if role_key == 'payout_manager' else 'Payout Mgr'}",
                callback_data=f"adm:ctrl:preset:{target_uid}:payout_manager",
                style="success" if role_key == "payout_manager" else "primary",
            ),
        ],
        [
            create_button(
                f"{'• Super Admin •' if role_key == 'super_admin' else 'Super Admin'}",
                callback_data=f"adm:ctrl:preset:{target_uid}:super_admin",
                style="success" if role_key == "super_admin" else "primary",
            ),
            create_button(
                f"{'• Custom •' if role_key == 'custom' else 'Custom'}",
                callback_data=f"adm:ctrl:preset:{target_uid}:custom",
                style="success" if role_key == "custom" else "primary",
            ),
        ],
    ]

    for i in range(0, len(ADMIN_PERMISSIONS), 2):
        row = []
        for p_key, p_label in ADMIN_PERMISSIONS[i:i + 2]:
            on = bool(perms.get(p_key, False))
            short_lbl = strip_all_emojis(p_label) or p_label
            btn_lbl = f"{'✅' if on else '❌'} {short_lbl}"
            row.append(create_button(
                btn_lbl,
                callback_data=f"adm:ctrl:perm:{target_uid}:{p_key}",
                style="success" if on else "danger",
            ))
        buttons.append(row)

    buttons.append([_admin_inline_btn(
        "Remove Admin", callback_data=f"adm:delconf:{target_uid}",
        style="danger", emoji_id="5422557736330106570",
        fallback_emoji="🗑️", use_premium=use_premium,
    )])
    buttons.append([_admin_inline_btn(
        "Back", callback_data="adm:ctrl:list",
        style="primary", emoji_id="5456187398977247949",
        fallback_emoji="◀️", use_premium=use_premium,
    )])
    return text, InlineKeyboardMarkup(buttons)


def build_admin_role_picker_view(target_uid: int, admin_name: str):
    text = (
        f"✅ Admin **{escape_md(admin_name)}** (`{target_uid}`) added!\n\n"
        "🎭 **SELECT ROLE / PERMISSION PRESET:**\n"
        "• **Support:** Services, Broadcast, Live Receivers\n"
        "• **Payout Manager:** Manage Payouts, Withdraw Settings\n"
        "• **Super Admin:** All Permissions\n"
        "• **Custom:** Choose permissions manually"
    )
    buttons = [
        [
            create_button("🎧 Support", callback_data=f"adm:add:role:{target_uid}:support", style="primary"),
            create_button("💰 Payout Manager", callback_data=f"adm:add:role:{target_uid}:payout_manager", style="primary"),
        ],
        [
            create_button("🛡️ Super Admin", callback_data=f"adm:add:role:{target_uid}:super_admin", style="success"),
            create_button("⚙️ Custom", callback_data=f"adm:add:role:{target_uid}:custom", style="danger"),
        ],
    ]
    return text, InlineKeyboardMarkup(buttons)


def _format_relative_time(ts: float) -> str:
    diff = max(0, int(time.time() - ts))
    if diff < 5:
        return "just now"
    if diff < 60:
        return f"{diff}s ago"
    if diff < 3600:
        return f"{diff // 60}m ago"
    if diff < 86400:
        return f"{diff // 3600}h ago"
    return f"{diff // 86400}d ago"


def _is_missing_table_error(err: Exception, table_name: str) -> bool:
    msg = str(err).lower()
    return (
        "pgrst205" in msg
        or "42p01" in msg
        or "does not exist" in msg
        or "could not find the table" in msg
        or (table_name.lower() in msg and ("not found" in msg or "schema cache" in msg))
    )


def _normalize_live_event(ev: dict, default_ts: Optional[float] = None) -> dict:
    ts_val = float(ev.get("ts") or (default_ts if default_ts is not None else time.time()))
    return {
        "user_id": int(ev.get("user_id") or 0),
        "first_name": str(ev.get("first_name") or "")[:64],
        "username": str(ev.get("username") or "").strip().lstrip("@")[:64],
        "service": str(ev.get("service") or "Service")[:64],
        "country": str(ev.get("country") or "Unknown")[:64],
        "number": str(ev.get("number") or "")[:40],
        "otp_code": str(ev.get("otp_code") or "")[:32],
        "payout": float(ev.get("payout") or 0.0),
        "ts": ts_val,
    }


def _read_live_events_fallback_list() -> list:
    raw = get_setting(_LIVE_EVENTS_FALLBACK_KEY, "")
    if not raw:
        return []
    try:
        parsed = json.loads(raw)
        if isinstance(parsed, list):
            return parsed
    except Exception:
        pass
    return []


def _write_live_events_fallback_list(items: list):
    cutoff = time.time() - LIVE_RECEIVERS_RETENTION_SECONDS
    pruned = [ev for ev in items if float(ev.get("ts") or 0) >= cutoff]
    pruned.sort(key=lambda ev: float(ev.get("ts") or 0), reverse=True)
    if len(pruned) > LIVE_RECEIVERS_MAX_EVENTS:
        pruned = pruned[:LIVE_RECEIVERS_MAX_EVENTS]
    set_setting(_LIVE_EVENTS_FALLBACK_KEY, json.dumps(pruned, separators=(",", ":")))


def record_live_receiver_events_batch_sync(events: list):
    global _LIVE_EVENTS_TABLE_MISSING
    if not events:
        return
    now = time.time()
    clean_events = [_normalize_live_event(ev, default_ts=now) for ev in events if ev.get("user_id")]
    if not clean_events:
        return

    if not _LIVE_EVENTS_TABLE_MISSING:
        try:
            supabase.table("live_otp_events").insert(clean_events).execute()
            return
        except Exception as e:
            if _is_missing_table_error(e, "live_otp_events"):
                with _LIVE_EVENTS_LOCK:
                    if not _LIVE_EVENTS_TABLE_MISSING:
                        logger.warning(
                            "Table 'live_otp_events' not found in Supabase; using 'settings' fallback until table is created."
                        )
                        _LIVE_EVENTS_TABLE_MISSING = True
            else:
                logger.error(f"record_live_receiver_events_batch_sync error: {e}")
                return

    with _LIVE_EVENTS_LOCK:
        existing = _read_live_events_fallback_list()
        existing.extend(clean_events)
        _write_live_events_fallback_list(existing)


def get_live_receiver_events_sync(
    filter_mode: str = "all",
    limit: int = LIVE_RECEIVERS_MAX_EVENTS,
) -> list:
    global _LIVE_EVENTS_TABLE_MISSING
    if filter_mode not in ("5m", "15m", "30m", "1h", "all"):
        filter_mode = "all"
    window_sec = {
        "5m": 300,
        "15m": 900,
        "30m": 1800,
        "1h": 3600,
        "all": LIVE_RECEIVERS_RETENTION_SECONDS,
    }[filter_mode]
    cutoff = time.time() - window_sec
    safe_limit = max(1, min(int(limit or LIVE_RECEIVERS_MAX_EVENTS), LIVE_RECEIVERS_MAX_EVENTS))

    if not _LIVE_EVENTS_TABLE_MISSING:
        try:
            r = (
                supabase.table("live_otp_events")
                .select("user_id, first_name, username, service, country, number, otp_code, payout, ts")
                .gte("ts", cutoff)
                .order("ts", desc=True)
                .limit(safe_limit)
                .execute()
            )
            return r.data or []
        except Exception as e:
            if _is_missing_table_error(e, "live_otp_events"):
                with _LIVE_EVENTS_LOCK:
                    if not _LIVE_EVENTS_TABLE_MISSING:
                        logger.warning(
                            "Table 'live_otp_events' not found in Supabase; reading from 'settings' fallback."
                        )
                        _LIVE_EVENTS_TABLE_MISSING = True
            else:
                logger.error(f"get_live_receiver_events_sync error: {e}")
                return []

    with _LIVE_EVENTS_LOCK:
        items = _read_live_events_fallback_list()
    filtered = [ev for ev in items if float(ev.get("ts") or 0) >= cutoff]
    filtered.sort(key=lambda ev: float(ev.get("ts") or 0), reverse=True)
    return filtered[:safe_limit]


def cleanup_old_live_receiver_events_sync():
    global _LIVE_EVENTS_TABLE_MISSING
    cutoff = time.time() - LIVE_RECEIVERS_RETENTION_SECONDS
    if not _LIVE_EVENTS_TABLE_MISSING:
        try:
            supabase.table("live_otp_events").delete().lt("ts", cutoff).execute()
        except Exception as e:
            if _is_missing_table_error(e, "live_otp_events"):
                with _LIVE_EVENTS_LOCK:
                    _LIVE_EVENTS_TABLE_MISSING = True
            else:
                logger.error(f"cleanup_old_live_receiver_events_sync error: {e}")
    with _LIVE_EVENTS_LOCK:
        raw = get_setting(_LIVE_EVENTS_FALLBACK_KEY, "")
        if raw:
            existing = _read_live_events_fallback_list()
            kept = [ev for ev in existing if float(ev.get("ts") or 0) >= cutoff]
            if len(kept) != len(existing):
                _write_live_events_fallback_list(kept)


def _filter_live_events(filter_mode: str = "all") -> list:
    return get_live_receiver_events_sync(filter_mode, limit=LIVE_RECEIVERS_MAX_EVENTS)


def _truncate_text(val: str, max_len: int) -> str:
    val = str(val or "").strip()
    if len(val) <= max_len:
        return val
    return val[: max(1, max_len - 1)].rstrip() + "…"


def _format_live_service(raw_service: str, use_premium: bool) -> str:
    clean_srv = _cb_clean(raw_service or "Service") or "Service"
    clean_srv = _truncate_text(clean_srv, 22)
    if use_premium:
        # Preserve a leading <tg-emoji> icon if the service name itself starts with one
        m = re.match(r'^(\s*<tg-emoji emoji-id="\d+">.*?</tg-emoji>\s*)', str(raw_service or ""))
        if m:
            return f"{m.group(1).strip()} {html.escape(clean_srv)}".strip()
    return html.escape(clean_srv)


def build_live_receivers_view(
    filter_mode: str = "all",
    page: int = 1,
    use_premium: Optional[bool] = None,
    events: Optional[list] = None,
) -> Tuple[str, InlineKeyboardMarkup]:
    premium = _is_premium_emojis_enabled(use_premium)
    if filter_mode not in ("5m", "15m", "30m", "1h", "all"):
        filter_mode = "all"

    if events is None:
        events = _filter_live_events(filter_mode)
    total_events = len(events)
    unique_receivers = len({ev["user_id"] for ev in events})

    per_page = 25
    total_pages = max(1, (total_events + per_page - 1) // per_page)
    page = max(1, min(page, total_pages))
    start_idx = (page - 1) * per_page
    page_events = events[start_idx:start_idx + per_page]

    filter_labels = {
        "5m": "Last 5m",
        "15m": "Last 15m",
        "30m": "Last 30m",
        "1h": "Last 1h",
        "all": "All Recent",
    }
    now_bd = datetime.datetime.now(_BD_TZ).strftime("%H:%M:%S")

    e_live = _tg_emoji("5352877703043258544", "📡", premium)
    e_search = _tg_emoji("5352922460897452503", "🔍", premium)
    e_msg = _tg_emoji("5472239203590888751", "📨", premium)
    e_group = _tg_emoji("6307589808424228455", "👥", premium)
    e_clock = _tg_emoji("5472239203590888751", "⏱️", premium)
    e_globe = _tg_emoji("5375177250553487549", "🌍", premium)
    e_tag = _tg_emoji("5258096772776991776", "🏷️", premium)
    e_phone = _tg_emoji("5404435834789187002", "📞", premium)
    e_user = _tg_emoji("6307589808424228455", "👤", premium)

    text = (
        f"{e_live} <b>LIVE OTP RECEIVERS</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{e_search} {filter_labels[filter_mode]} • "
        f"{e_msg} {total_events} • "
        f"{e_group} {unique_receivers}\n"
        f"{e_clock} {now_bd} • Page {page}/{total_pages}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
    )

    if not page_events:
        text += (
            "\n<i>No live OTPs recorded yet for this window.</i>\n"
            "<i>Incoming OTPs will appear here automatically as users receive them.</i>\n"
        )
    else:
        plain_len = len(re.sub(r'<[^>]+>', '', text))
        for idx, ev in enumerate(page_events, start=start_idx + 1):
            uid = ev["user_id"]
            fname = _truncate_text(ev.get("first_name") or f"User {uid}", 24)
            uname = (ev.get("username") or "").strip().lstrip("@")
            user_link = f'<a href="tg://user?id={uid}">{html.escape(fname)}</a>'
            uname_part = f" (@{html.escape(_truncate_text(uname, 24))})" if uname else ""

            service = _format_live_service(ev.get("service") or "Service", premium)
            raw_country = strip_all_emojis(ev.get("country") or "") or str(ev.get("country") or "Unknown")
            country = html.escape(_truncate_text(raw_country, 16))
            number = html.escape(str(ev.get("number") or ""))
            ts = float(ev.get("ts") or time.time())
            bd_time = datetime.datetime.fromtimestamp(ts, _BD_TZ).strftime("%H:%M:%S")
            rel_time = _format_relative_time(ts)

            entry = (
                f"\n{idx}. {e_globe} {country} {e_tag} {service} • {e_phone} {number} • {e_clock} {rel_time} ({bd_time})\n"
                f"    - {e_user} {user_link}{uname_part}\n"
            )
            entry_plain_len = len(re.sub(r'<[^>]+>', '', entry))
            if plain_len + entry_plain_len > 3950:
                text += "\n<i>…trimmed to fit Telegram message limit.</i>\n"
                break
            text += entry
            plain_len += entry_plain_len

    def _fbtn(mode: str, lbl: str):
        is_active = (filter_mode == mode)
        btn_text = f"• {lbl} •" if is_active else lbl
        return _admin_inline_btn(
            btn_text,
            callback_data=f"adm:live:page:{mode}:1",
            style="success" if is_active else "primary",
            emoji_id="5472239203590888751" if mode != "all" else "5352922460897452503",
            fallback_emoji="⏱️" if mode != "all" else "🔍",
            use_premium=premium,
        )

    buttons = [
        [_fbtn("5m", "5m"), _fbtn("15m", "15m"), _fbtn("30m", "30m")],
        [
            _fbtn("1h", "1h"),
            _fbtn("all", "All"),
            _admin_inline_btn(
                "Refresh",
                callback_data=f"adm:live:page:{filter_mode}:{page}",
                style="success",
                emoji_id="5244758760429213978",
                fallback_emoji="🔄",
                use_premium=premium,
            ),
        ],
        [
            _admin_inline_btn(
                "Active Summary",
                callback_data=f"adm:live:summary:{filter_mode}:1",
                style="primary",
                emoji_id="6307589808424228455",
                fallback_emoji="👥",
                use_premium=premium,
            ),
        ],
    ]

    if total_pages > 1:
        nav_row = []
        if page > 1:
            nav_row.append(_admin_inline_btn(
                "Prev",
                callback_data=f"adm:live:page:{filter_mode}:{page - 1}",
                style="primary",
                emoji_id="5456187398977247949",
                fallback_emoji="◀️",
                use_premium=premium,
            ))
        nav_row.append(create_button(f"{page}/{total_pages}", callback_data="noop", style="primary"))
        if page < total_pages:
            nav_row.append(_admin_inline_btn(
                "Next",
                callback_data=f"adm:live:page:{filter_mode}:{page + 1}",
                style="primary",
                emoji_id="5370604433233177619",
                fallback_emoji="▶️",
                use_premium=premium,
                emoji_after=True,
            ))
        buttons.append(nav_row)

    return text, InlineKeyboardMarkup(buttons)


def build_live_receivers_summary_view(
    filter_mode: str = "all",
    page: int = 1,
    use_premium: Optional[bool] = None,
    events: Optional[list] = None,
) -> Tuple[str, InlineKeyboardMarkup]:
    premium = _is_premium_emojis_enabled(use_premium)
    if filter_mode not in ("5m", "15m", "30m", "1h", "all"):
        filter_mode = "all"

    if events is None:
        events = _filter_live_events(filter_mode)
    by_user: Dict[int, dict] = {}
    for ev in events:
        uid = ev["user_id"]
        if uid not in by_user:
            by_user[uid] = {
                "user_id": uid,
                "first_name": ev.get("first_name") or f"User {uid}",
                "username": (ev.get("username") or "").strip().lstrip("@"),
                "count": 0,
                "last_ts": float(ev.get("ts") or 0),
                "last_service": ev.get("service") or "Service",
                "last_country": ev.get("country") or "Unknown",
                "last_number": ev.get("number") or "",
            }
        by_user[uid]["count"] += 1

    grouped = sorted(by_user.values(), key=lambda x: x["last_ts"], reverse=True)
    total_users = len(grouped)
    total_otps = len(events)

    per_page = 25
    total_pages = max(1, (total_users + per_page - 1) // per_page)
    page = max(1, min(page, total_pages))
    start_idx = (page - 1) * per_page
    page_items = grouped[start_idx:start_idx + per_page]

    filter_labels = {
        "5m": "Last 5m",
        "15m": "Last 15m",
        "30m": "Last 30m",
        "1h": "Last 1h",
        "all": "All Recent",
    }
    now_bd = datetime.datetime.now(_BD_TZ).strftime("%H:%M:%S")

    e_group = _tg_emoji("6307589808424228455", "👥", premium)
    e_search = _tg_emoji("5352922460897452503", "🔍", premium)
    e_msg = _tg_emoji("5472239203590888751", "📨", premium)
    e_clock = _tg_emoji("5472239203590888751", "⏱️", premium)
    e_user = _tg_emoji("6307589808424228455", "👤", premium)

    text = (
        f"{e_group} <b>ACTIVE LIVE RECEIVERS SUMMARY</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{e_search} {filter_labels[filter_mode]} • "
        f"{e_group} {total_users} • "
        f"{e_msg} {total_otps}\n"
        f"{e_clock} {now_bd} • Page {page}/{total_pages}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
    )

    if not page_items:
        text += "\n<i>No active receivers found for this time window.</i>\n"
    else:
        plain_len = len(re.sub(r'<[^>]+>', '', text))
        for idx, rec in enumerate(page_items, start=start_idx + 1):
            uid = rec["user_id"]
            fname = _truncate_text(rec["first_name"], 24)
            user_link = f'<a href="tg://user?id={uid}">{html.escape(fname)}</a>'
            uname_part = f" (@{html.escape(_truncate_text(rec['username'], 24))})" if rec["username"] else ""
            service = _format_live_service(rec["last_service"], premium)
            raw_country = strip_all_emojis(rec["last_country"]) or str(rec["last_country"])
            country = html.escape(_truncate_text(raw_country, 16))
            number = html.escape(str(rec["last_number"]))
            rel_time = _format_relative_time(rec["last_ts"])

            entry = (
                f"\n{idx}. {e_user} {user_link}{uname_part} — <b>{rec['count']} OTP</b>\n"
                f"    - {country} {service} • {number} ({rel_time})\n"
            )
            entry_plain_len = len(re.sub(r'<[^>]+>', '', entry))
            if plain_len + entry_plain_len > 3950:
                text += "\n<i>…trimmed to fit Telegram message limit.</i>\n"
                break
            text += entry
            plain_len += entry_plain_len

    def _fbtn(mode: str, lbl: str):
        is_active = (filter_mode == mode)
        btn_text = f"• {lbl} •" if is_active else lbl
        return _admin_inline_btn(
            btn_text,
            callback_data=f"adm:live:summary:{mode}:1",
            style="success" if is_active else "primary",
            emoji_id="5472239203590888751" if mode != "all" else "5352922460897452503",
            fallback_emoji="⏱️" if mode != "all" else "🔍",
            use_premium=premium,
        )

    buttons = [
        [_fbtn("5m", "5m"), _fbtn("15m", "15m"), _fbtn("30m", "30m")],
        [
            _fbtn("1h", "1h"),
            _fbtn("all", "All"),
            _admin_inline_btn(
                "Refresh",
                callback_data=f"adm:live:summary:{filter_mode}:{page}",
                style="success",
                emoji_id="5244758760429213978",
                fallback_emoji="🔄",
                use_premium=premium,
            ),
        ],
        [
            _admin_inline_btn(
                "Live Stream",
                callback_data=f"adm:live:page:{filter_mode}:1",
                style="primary",
                emoji_id="5352877703043258544",
                fallback_emoji="📡",
                use_premium=premium,
            ),
        ],
    ]

    if total_pages > 1:
        nav_row = []
        if page > 1:
            nav_row.append(_admin_inline_btn(
                "Prev",
                callback_data=f"adm:live:summary:{filter_mode}:{page - 1}",
                style="primary",
                emoji_id="5456187398977247949",
                fallback_emoji="◀️",
                use_premium=premium,
            ))
        nav_row.append(create_button(f"{page}/{total_pages}", callback_data="noop", style="primary"))
        if page < total_pages:
            nav_row.append(_admin_inline_btn(
                "Next",
                callback_data=f"adm:live:summary:{filter_mode}:{page + 1}",
                style="primary",
                emoji_id="5370604433233177619",
                fallback_emoji="▶️",
                use_premium=premium,
                emoji_after=True,
            ))
        buttons.append(nav_row)

    return text, InlineKeyboardMarkup(buttons)


def build_user_manager_view(use_premium: Optional[bool] = None, user_id: int = 0):
    text = "👥 **USER MANAGER**\n\nManage users, control admins, view global statistics, or export the database."
    buttons = []
    can_users = (user_id == 0) or has_admin_perm_sync(user_id, "users")
    can_admins = (user_id == 0) or has_admin_perm_sync(user_id, "admins")
    if can_users:
        buttons.append([_admin_inline_btn("User Control", callback_data="adm:usr:control", style="primary", emoji_id="6307589808424228455", fallback_emoji="👥", use_premium=use_premium)])
    if can_admins:
        buttons.append([_admin_inline_btn("Admin Control", callback_data="adm:ctrl:list", style="primary", emoji_id="5258508428212445001", fallback_emoji="🛡️", use_premium=use_premium)])
    if can_users:
        buttons.append([_admin_inline_btn("Statistics", callback_data="adm:usr:stats", style="primary", emoji_id="5352877703043258544", fallback_emoji="📊", use_premium=use_premium)])
        buttons.append([_admin_inline_btn("Export Users (JSON)", callback_data="adm:usr:export", style="success", emoji_id="6039573425268201570", fallback_emoji="📤", use_premium=use_premium)])
    buttons.append([_admin_inline_btn("Back to Panel", callback_data="adm:panel_back", style="danger", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium)])
    return text, InlineKeyboardMarkup(buttons)


def build_user_control_view(use_premium: Optional[bool] = None):
    text = "👥 **USER CONTROL**\n\nSearch specific users, browse all/banned/inactive users, or configure Auto Ban rules."
    buttons = [
        [_admin_inline_btn("Search User", callback_data="adm:usr:search", style="primary", emoji_id="5352922460897452503", fallback_emoji="🔍", use_premium=use_premium)],
        [
            _admin_inline_btn("All Users", callback_data="adm:usr:all:recent:1", style="primary", emoji_id="6307589808424228455", fallback_emoji="👥", use_premium=use_premium),
            _admin_inline_btn("Banned Users", callback_data="adm:usr:banned:1", style="danger", emoji_id="5422557736330106570", fallback_emoji="🚫", use_premium=use_premium),
        ],
        [
            _admin_inline_btn("Inactive Users", callback_data="adm:usr:inactive:7d:1", style="primary", emoji_id="5472239203590888751", fallback_emoji="⏳", use_premium=use_premium),
            _admin_inline_btn("Auto Ban System", callback_data="adm:usr:autoban", style="danger", emoji_id="5258096772776991776", fallback_emoji="🛡️", use_premium=use_premium),
        ],
        [_admin_inline_btn("Back", callback_data="adm:usr:manager", style="danger", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium)],
    ]
    return text, InlineKeyboardMarkup(buttons)


def _encode_usr_back(back_cb: str) -> str:
    if back_cb.startswith("adm:usr:all:"):
        parts = back_cb.split(":")
        sort_short = "o" if (len(parts) > 3 and parts[3] == "old") else "r"
        page = parts[4] if len(parts) > 4 else "1"
        return f"a:{sort_short}:{page}"
    if back_cb.startswith("adm:usr:banned:"):
        page = back_cb.split(":")[-1] or "1"
        return f"b:{page}"
    if back_cb.startswith("adm:usr:inactive:"):
        parts = back_cb.split(":")
        win = parts[3] if len(parts) > 3 else "7d"
        page = parts[4] if len(parts) > 4 else "1"
        return f"i:{win}:{page}"
    return "c"


def _decode_usr_back(tok: str) -> str:
    if not tok or tok == "c":
        return "adm:usr:control"
    parts = tok.split(":")
    if parts[0] == "a":
        sort_mode = "old" if (len(parts) > 1 and parts[1] == "o") else "recent"
        page = parts[2] if len(parts) > 2 else "1"
        return f"adm:usr:all:{sort_mode}:{page}"
    if parts[0] == "b":
        page = parts[1] if len(parts) > 1 else "1"
        return f"adm:usr:banned:{page}"
    if parts[0] == "i":
        win = parts[1] if len(parts) > 1 else "7d"
        page = parts[2] if len(parts) > 2 else "1"
        return f"adm:usr:inactive:{win}:{page}"
    return "adm:usr:control"


def build_all_users_view(sort_mode: str = "recent", page: int = 1, use_premium: Optional[bool] = None, users: Optional[list] = None):
    if sort_mode not in ("recent", "old"):
        sort_mode = "recent"
    if users is None:
        users = get_users_ordered_sync(sort_mode)
    total = len(users)
    per_page = 25
    total_pages = max(1, (total + per_page - 1) // per_page)
    page = max(1, min(page, total_pages))
    start_idx = (page - 1) * per_page
    page_items = users[start_idx:start_idx + per_page]

    sort_lbl = "Recent Joined" if sort_mode == "recent" else "Old Users"
    text = (
        "👥 **ALL USERS**\n"
        f"Total: `{total}` • Sort: `{sort_lbl}` • Page `{page}/{total_pages}`\n\n"
        "Tap a user below to view summary & Ban/Unban:"
    )

    back_tok = f"a:{'o' if sort_mode == 'old' else 'r'}:{page}"
    buttons = []
    for u in page_items:
        uid = int(u.get("user_id") or 0)
        if not uid:
            continue
        fname = _truncate_text(str(u.get("first_name") or u.get("username") or f"User {uid}"), 22)
        bal = fmt_num(u.get("balance", 0))
        is_ban = bool(u.get("is_banned")) or (uid in _IN_MEMORY_BANNED)
        prefix = "🚫 " if is_ban else ""
        buttons.append([create_button(
            f"{prefix}{fname} ({bal}৳)",
            callback_data=f"adm:usr:view:{uid}:{back_tok}",
            style="danger" if is_ban else "primary",
        )])

    buttons.append([
        create_button(
            f"{'• Recent Joined •' if sort_mode == 'recent' else 'Recent Joined'}",
            callback_data="adm:usr:all:recent:1",
            style="success" if sort_mode == "recent" else "primary",
        ),
        create_button(
            f"{'• Old Users •' if sort_mode == 'old' else 'Old Users'}",
            callback_data="adm:usr:all:old:1",
            style="success" if sort_mode == "old" else "primary",
        ),
    ])

    if total_pages > 1:
        nav = []
        if page > 1:
            nav.append(_admin_inline_btn("Prev", callback_data=f"adm:usr:all:{sort_mode}:{page - 1}", style="primary", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium))
        nav.append(create_button(f"{page}/{total_pages}", callback_data="noop", style="primary"))
        if page < total_pages:
            nav.append(_admin_inline_btn("Next", callback_data=f"adm:usr:all:{sort_mode}:{page + 1}", style="primary", emoji_id="5370604433233177619", fallback_emoji="▶️", use_premium=use_premium, emoji_after=True))
        buttons.append(nav)

    buttons.append([_admin_inline_btn("Back", callback_data="adm:usr:control", style="danger", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium)])
    return text, InlineKeyboardMarkup(buttons)


def build_banned_users_view(page: int = 1, use_premium: Optional[bool] = None, users: Optional[list] = None):
    if users is None:
        users = get_banned_users_list_sync()
    total = len(users)
    per_page = 25
    total_pages = max(1, (total + per_page - 1) // per_page)
    page = max(1, min(page, total_pages))
    start_idx = (page - 1) * per_page
    page_items = users[start_idx:start_idx + per_page]

    text = (
        "🚫 **BANNED USERS**\n"
        f"Total Banned: `{total}` • Page `{page}/{total_pages}`\n\n"
        + ("Tap a user below to inspect or Unban:" if page_items else "_No banned users found._")
    )

    back_tok = f"b:{page}"
    buttons = []
    for u in page_items:
        uid = int(u.get("user_id") or 0)
        if not uid:
            continue
        fname = _truncate_text(str(u.get("first_name") or u.get("username") or f"User {uid}"), 22)
        bal = fmt_num(u.get("balance", 0))
        buttons.append([create_button(
            f"🚫 {fname} ({bal}৳)",
            callback_data=f"adm:usr:view:{uid}:{back_tok}",
            style="danger",
        )])

    if total_pages > 1:
        nav = []
        if page > 1:
            nav.append(_admin_inline_btn("Prev", callback_data=f"adm:usr:banned:{page - 1}", style="primary", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium))
        nav.append(create_button(f"{page}/{total_pages}", callback_data="noop", style="primary"))
        if page < total_pages:
            nav.append(_admin_inline_btn("Next", callback_data=f"adm:usr:banned:{page + 1}", style="primary", emoji_id="5370604433233177619", fallback_emoji="▶️", use_premium=use_premium, emoji_after=True))
        buttons.append(nav)

    buttons.append([_admin_inline_btn("Back", callback_data="adm:usr:control", style="danger", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium)])
    return text, InlineKeyboardMarkup(buttons)


def build_inactive_users_view(window: str = "7d", page: int = 1, use_premium: Optional[bool] = None, users: Optional[list] = None):
    if window not in ("24h", "3d", "7d", "15d", "30d"):
        window = "7d"
    if users is None:
        users = get_inactive_users_list_sync(window)
    total = len(users)
    per_page = 25
    total_pages = max(1, (total + per_page - 1) // per_page)
    page = max(1, min(page, total_pages))
    start_idx = (page - 1) * per_page
    page_items = users[start_idx:start_idx + per_page]

    text = (
        "⏳ **INACTIVE USERS**\n"
        f"Filter: `No OTP in {window}` or `< 10 weekly OTPs`\n"
        f"Matched: `{total}` • Page `{page}/{total_pages}`\n\n"
        + ("Tap a user below to view summary & Ban/Unban:" if page_items else "_No inactive users matched for this window._")
    )

    back_tok = f"i:{window}:{page}"
    buttons = []
    for u in page_items:
        uid = int(u.get("user_id") or 0)
        if not uid:
            continue
        fname = _truncate_text(str(u.get("first_name") or u.get("username") or f"User {uid}"), 20)
        days = int(u.get("_inactive_days", 0))
        days_lbl = "Never" if days >= 9999 else f"{days}d inactive"
        is_ban = bool(u.get("is_banned")) or (uid in _IN_MEMORY_BANNED)
        prefix = "🚫 " if is_ban else ""
        buttons.append([create_button(
            f"{prefix}{fname} ({days_lbl})",
            callback_data=f"adm:usr:view:{uid}:{back_tok}",
            style="danger" if is_ban else "primary",
        )])

    def _wbtn(w: str, lbl: str):
        active = (window == w)
        return create_button(
            f"• {lbl} •" if active else lbl,
            callback_data=f"adm:usr:inactive:{w}:1",
            style="success" if active else "primary",
        )

    buttons.append([_wbtn("24h", "24h"), _wbtn("3d", "3d"), _wbtn("7d", "7d")])
    buttons.append([
        _wbtn("15d", "15d"),
        _wbtn("30d", "30d"),
        _admin_inline_btn("Refresh", callback_data=f"adm:usr:inactive:{window}:{page}", style="success", emoji_id="5244758760429213978", fallback_emoji="🔄", use_premium=use_premium),
    ])

    if total_pages > 1:
        nav = []
        if page > 1:
            nav.append(_admin_inline_btn("Prev", callback_data=f"adm:usr:inactive:{window}:{page - 1}", style="primary", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium))
        nav.append(create_button(f"{page}/{total_pages}", callback_data="noop", style="primary"))
        if page < total_pages:
            nav.append(_admin_inline_btn("Next", callback_data=f"adm:usr:inactive:{window}:{page + 1}", style="primary", emoji_id="5370604433233177619", fallback_emoji="▶️", use_premium=use_premium, emoji_after=True))
        buttons.append(nav)

    buttons.append([_admin_inline_btn("Back", callback_data="adm:usr:control", style="danger", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium)])
    return text, InlineKeyboardMarkup(buttons)


def build_autoban_settings_view(use_premium: Optional[bool] = None):
    abuse_on = is_abuse_autoban_enabled()
    thresh = get_abuse_ban_threshold()
    window_s = get_abuse_ban_window()

    inact_on = is_inactive_autoban_enabled()
    inact_days = get_inactive_autoban_days()
    inact_otps = get_inactive_autoban_min_otps()

    text = (
        "🛡️ **AUTO BAN SYSTEM**\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"🔁 **Number-Change Abuse Ban:** `{'ENABLED 🟢' if abuse_on else 'DISABLED 🔴'}`\n"
        f"   • Limit: `{thresh}` changes in `{window_s}s`\n\n"
        f"⏳ **Inactive User Auto-Ban:** `{'ENABLED 🟢' if inact_on else 'DISABLED 🔴'}`\n"
        f"   • Rule: Inactive `>= {inact_days}d` & Weekly OTPs `< {inact_otps}`"
    )
    buttons = [
        [create_button(
            f"Abuse Auto-Ban: {'ENABLED 🟢' if abuse_on else 'DISABLED 🔴'}",
            callback_data="adm:usr:ab:tog_abuse",
            style="success" if abuse_on else "danger",
        )],
        [
            create_button(f"Max Changes ({thresh})", callback_data="adm:usr:ab:set_thresh", style="primary"),
            create_button(f"Window ({window_s}s)", callback_data="adm:usr:ab:set_win", style="primary"),
        ],
        [create_button(
            f"Inactive Auto-Ban: {'ENABLED 🟢' if inact_on else 'DISABLED 🔴'}",
            callback_data="adm:usr:ab:tog_inact",
            style="success" if inact_on else "danger",
        )],
        [
            create_button(f"Inactive Days ({inact_days}d)", callback_data="adm:usr:ab:set_days", style="primary"),
            create_button(f"Min Weekly OTPs ({inact_otps})", callback_data="adm:usr:ab:set_otps", style="primary"),
        ],
        [create_button("⚡ Run Inactive Ban Sweep Now", callback_data="adm:usr:ab:run_now", style="danger")],
        [_admin_inline_btn("Back", callback_data="adm:usr:control", style="primary", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=use_premium)],
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_stats_view():
    stats = get_global_stats_sync()
    if not stats:
        return "❌ Failed to load statistics.", InlineKeyboardMarkup([[create_button("Back", callback_data="adm:usr:manager", style="danger", icon_custom_emoji_id="5456187398977247949")]])

    text = (
        "📊 **GLOBAL BOT STATISTICS**\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 **Total Users:** `{stats['total_users']}`\n"
        f"💰 **Total Current Balance:** `{fmt_num(stats['total_balance'])} ৳`\n"
        f"📈 **Lifetime Earned:** `{fmt_num(stats['total_earned'])} ৳`\n"
        f"📅 **Today's Earned:** `{fmt_num(stats['today_today'])} ৳`\n" if False else
        "📊 **GLOBAL BOT STATISTICS**\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 **Total Users:** `{stats['total_users']}`\n"
        f"💰 **Total Current Balance:** `{fmt_num(stats['total_balance'])} ৳`\n"
        f"📈 **Lifetime Earned:** `{fmt_num(stats['total_earned'])} ৳`\n"
        f"📅 **Today's Earned:** `{fmt_num(stats['total_today'])} ৳`\n"
        f"🎁 **Total Referral Earned:** `{fmt_num(stats['total_refer'])} ৳`\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"📨 **Lifetime OTPs:** `{stats['total_otps']}`\n"
        f"📊 **Weekly OTPs (Last 7 Days):** `{stats['total_weekly_otps']}`\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "⚠️ *Note: Exact 30-day earnings cannot be calculated without historical daily data, but lifetime and weekly data are accurate.*"
    )

    buttons = [
        [create_button("Refresh Stats", callback_data="adm:usr:stats", style="success", icon_custom_emoji_id="5244758760429213978")],
        [create_button("Back to User Manager", callback_data="adm:usr:manager", style="danger", icon_custom_emoji_id="5456187398977247949")]
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_admin_services_view():
    summary = get_admin_services_summary()
    if not summary:
        text = "📱 <b>SERVICES MANAGEMENT</b>\n\nNo services added yet."
        buttons = [[create_button("Add New Service", callback_data="adm:srv:add", style="success", icon_custom_emoji_id="5287354223141342798")]]
        return text, InlineKeyboardMarkup(buttons)

    text = "📱 <b>SERVICES MANAGEMENT</b>\n\nSelect a service to manage:"
    buttons = []
    for srv, cnts in summary.items():
        srv_tok = _make_srv_token(srv)
        buttons.append([create_button(
            f"{srv} ({len(cnts)})",
            callback_data=f"adm:srv:view:{srv_tok}",
            style="primary",
            icon_custom_emoji_id="5258096772776991776",
        )])

    buttons.append([create_button("Add New Service / Numbers", callback_data="adm:srv:add", style="success", icon_custom_emoji_id="5287354223141342798")])
    return text, InlineKeyboardMarkup(buttons)


def build_service_manage_view(service: str):
    summary = get_admin_services_summary()
    cnts = summary.get(service, {})
    srv_tok = _make_srv_token(service)

    text = f"⚙️ <b>SERVICE DETAILS: {safe_html_escape(service)}</b>\n\n"
    text += "Select a country to manage:" if cnts else "No countries configured yet."

    buttons = []
    for cnt, count in cnts.items():
        payout = get_payout_sync(service, cnt)
        paused = is_country_paused_sync(service, cnt)
        paused_badge = " ⏸️" if paused else ""
        sc_tok = _make_sc_token(service, cnt)
        buttons.append([create_button(
            f"{cnt} ({count}) • {fmt_num(payout)}৳{paused_badge}",
            callback_data=f"adm:c:v:{sc_tok}",
            style="primary",
            icon_custom_emoji_id="5375177250553487549",
        )])

    buttons.append([create_button(
        "Add Country",
        callback_data=f"adm:srv:add:{srv_tok}",
        style="success",
        icon_custom_emoji_id="5287354223141342798",
    )])
    buttons.append([
        create_button("Edit Service", callback_data=f"adm:srv:edit:{srv_tok}", style="primary", icon_custom_emoji_id="5370604433233177619"),
        create_button("Delete Service", callback_data=f"adm:srv:delconf:{srv_tok}", style="danger", icon_custom_emoji_id="5422557736330106570"),
    ])
    buttons.append([create_button("Back to Services", callback_data="adm:srv:list", style="danger", icon_custom_emoji_id="5456187398977247949")])

    return text, InlineKeyboardMarkup(buttons)


def build_country_manage_view(service: str, country: str):
    summary = get_admin_services_summary()
    cnts = summary.get(service, {})
    avail = cnts.get(country, 0)
    payout = get_payout_sync(service, country)
    short = get_country_short_sync(service, country)
    cc_len = get_setting(f"cc_len:{service}:{country}", "0")
    paused = is_country_paused_sync(service, country)
    status_label = "⏸️ Paused" if paused else "▶️ Active"

    srv_tok = _make_srv_token(service)
    sc_tok = _make_sc_token(service, country)

    text = (
        f"🏳️ <b>COUNTRY DETAILS</b>\n\n"
        f"🏷️ <b>Service:</b> {safe_html_escape(service)}\n"
        f"🌍 <b>Country:</b> {safe_html_escape(country)}\n"
        f"🔤 <b>Short Name:</b> {safe_html_escape(short)}\n"
        f"📌 <b>Status:</b> {status_label}\n"
        f"📞 <b>Available Numbers:</b> <code>{avail}</code>\n"
        f"💰 <b>Payout:</b> <code>{fmt_num(payout)} ৳</code>\n"
        f"🔢 <b>Country Code Digit:</b> <code>{html.escape(str(cc_len))}</code>"
    )

    pause_btn = (
        create_button("Resume", callback_data=f"adm:c:togp:{sc_tok}", style="success", icon_custom_emoji_id="5370604433233177619")
        if paused else
        create_button("Pause", callback_data=f"adm:c:togp:{sc_tok}", style="primary", icon_custom_emoji_id="5472239203590888751")
    )

    buttons = [
        [create_button("Add Numbers", callback_data=f"adm:c:an:{sc_tok}", style="success", icon_custom_emoji_id="5287354223141342798")],
        [
            create_button("Edit", callback_data=f"adm:c:ed:{sc_tok}", style="primary", icon_custom_emoji_id="5370604433233177619"),
            create_button("Clear Stock", callback_data=f"adm:c:cconf:{sc_tok}", style="danger", icon_custom_emoji_id="5422557736330106570"),
        ],
        [
            pause_btn,
            create_button("Delete Country", callback_data=f"adm:c:dc:{sc_tok}", style="danger", icon_custom_emoji_id="5422557736330106570"),
        ],
        [create_button("Back", callback_data=f"adm:srv:view:{srv_tok}", style="danger", icon_custom_emoji_id="5456187398977247949")],
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_country_edit_view(service: str, country: str):
    payout = get_payout_sync(service, country)
    short = get_country_short_sync(service, country)
    cc_len = str(get_setting(f"cc_len:{service}:{country}", "0")).strip()
    sc_tok = _make_sc_token(service, country)

    text = (
        f"✏️ <b>EDIT COUNTRY</b>\n\n"
        f"🏷️ <b>Service:</b> {safe_html_escape(service)}\n"
        f"🌍 <b>Country Name:</b> {safe_html_escape(country)}\n"
        f"🔤 <b>Short Name:</b> {safe_html_escape(short)}\n"
        f"💰 <b>Payout:</b> <code>{fmt_num(payout)} ৳</code>\n"
        f"🔢 <b>Country Code Digit:</b> <code>{html.escape(cc_len)}</code>\n\n"
        f"Select what you want to edit:"
    )

    cc_row = []
    for d in ("2", "3", "4"):
        is_sel = (cc_len == d)
        cc_row.append(create_button(
            f"• CC: {d} •" if is_sel else f"CC: {d}",
            callback_data=f"adm:c:cc:{d}:{sc_tok}",
            style="success" if is_sel else "primary",
        ))

    buttons = [
        [create_button("Edit Name & Short", callback_data=f"adm:c:en:{sc_tok}", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Edit Payout", callback_data=f"adm:c:ep:{sc_tok}", style="primary", icon_custom_emoji_id="5417924076503062111")],
        cc_row,
        [create_button("Back", callback_data=f"adm:c:v:{sc_tok}", style="danger", icon_custom_emoji_id="5456187398977247949")],
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_payout_manage_view(service: str):
    cnts = get_admin_services_summary().get(service, {})
    text = f"💰 <b>PAYOUT MANAGEMENT: {safe_html_escape(service)}</b>\n\n"
    if cnts:
        for cnt in cnts.keys():
            payout = get_payout_sync(service, cnt)
            text += f"• <b>{safe_html_escape(cnt)}</b>: <code>{fmt_num(payout)} ৳</code>\n"
        text += "\n👉 Tap a country below to edit its payout amount."
    else:
        text += "No countries configured yet."

    buttons = []
    for cnt in cnts.keys():
        buttons.append([create_button(cnt, callback_data=f"adm:pay:edit:{_cb_clean(service)}:{_cb_clean(cnt)}", style="primary", icon_custom_emoji_id="5370604433233177619")])
    buttons.append([create_button("Back", callback_data=f"adm:srv:view:{_cb_clean(service)}", style="danger", icon_custom_emoji_id="5456187398977247949")])
    return text, InlineKeyboardMarkup(buttons)


def build_edit_links_view():
    ch_val = get_setting("channel", "https://t.me/your_channel")
    sp_val = get_setting("support", "@your_support")
    otp_link = get_setting("otp_group_link", "https://t.me/your_otp_group")
    otp_grp_id = get_setting("otp_group_id", OTP_GROUP_ID if OTP_GROUP_ID else "Not Set")
    dev_name = get_setting("dev_username", "developer")
    dev_link = get_setting("dev_link", "https://t.me/developer")

    text = (
        f"🔗 **EDIT LINKS & FORWARD SETTINGS**\n\n"
        f"📢 **Channel:** {escape_md(ch_val)}\n"
        f"🎧 **Support:** {escape_md(sp_val)}\n"
        f"🔗 **OTP Group Link:** {escape_md(otp_link)}\n"
        f"🆔 **OTP Forward Group ID:** `{escape_md(str(otp_grp_id))}`\n"
        f"👨‍💻 **Dev Name:** `{escape_md(dev_name)}`\n"
        f"🔗 **Dev Link:** {escape_md(dev_link)}\n\n"
        f"Click below to modify settings:"
    )
    buttons = [
        [create_button("Edit Channel", callback_data="adm:set:channel", style="primary", icon_custom_emoji_id="5370604433233177619"),
         create_button("Edit Support", callback_data="adm:set:support", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Edit Group Link", callback_data="adm:set:otplink", style="primary", icon_custom_emoji_id="5370604433233177619"),
         create_button("Edit Forward Group ID", callback_data="adm:set:otpgroupid", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Edit Dev Name", callback_data="adm:set:devname", style="primary", icon_custom_emoji_id="5370604433233177619"),
         create_button("Edit Dev Link", callback_data="adm:set:devlink", style="primary", icon_custom_emoji_id="5370604433233177619")]
    ]
    return text, InlineKeyboardMarkup(buttons)

def build_api_panels_view():
    panels = get_all_api_panels_sync()
    if not panels:
        text = "🌐 **API PANELS MANAGEMENT**\n\nNo API panels connected yet."
        buttons = [
            [create_button("Connect Standard Panel", callback_data="adm:api:add", style="success", icon_custom_emoji_id="5287354223141342798")],
            [create_button("Connect Custom API", callback_data="adm:api:add_custom", style="primary", icon_custom_emoji_id="5258096772776991776")],
            [create_button("Connect Captcha Panel", callback_data="adm:api:add_captcha", style="danger", icon_custom_emoji_id="5258508428212445001")],
            [create_button("Connect Augestel Panel", callback_data="adm:api:add_augestel", style="success", icon_custom_emoji_id="5287354223141342798")],
        ]
        return text, InlineKeyboardMarkup(buttons)

    text = "🌐 **API PANELS MANAGEMENT**\n\nConnected API Panels List:\n"
    buttons = []
    for p in panels:
        pid = p["id"]
        pname = p["name"]
        pinterval = p.get("polling_interval", 5.0)
        p_type = get_panel_type(p)
        tag = " 📡" if p_type == "augestel" else (" 🔐" if p_type == "captcha" else (" 🔧" if p_type == "custom" else ""))
        text += f"\n🔹 **{escape_md(pname)}**{tag} (Polling: `{pinterval}s`)"
        if p_type == "captcha":
            st = CAPTCHA_PANEL_STATUS.get(str(pid), "⏳ Pending login")
            text += f"\n   └ `{escape_md(st)}`"
        if p_type == "augestel":
            st = AUGESTEL_PANEL_STATUS.get(str(pid), "⏳ Pending login")
            text += f"\n   └ `{escape_md(st)}`"
        buttons.append([create_button(pname, callback_data=f"adm:api:view:{pid}", style="primary", icon_custom_emoji_id="5258096772776991776")])

    buttons.append([create_button("Connect Standard Panel", callback_data="adm:api:add", style="success", icon_custom_emoji_id="5287354223141342798")])
    buttons.append([create_button("Connect Custom API", callback_data="adm:api:add_custom", style="primary", icon_custom_emoji_id="5258096772776991776")])
    buttons.append([create_button("Connect Captcha Panel", callback_data="adm:api:add_captcha", style="danger", icon_custom_emoji_id="5258508428212445001")])
    buttons.append([create_button("Connect Augestel Panel", callback_data="adm:api:add_augestel", style="success", icon_custom_emoji_id="5287354223141342798")])
    return text, InlineKeyboardMarkup(buttons)

def build_panel_manage_view(panel_id: str):
    p = get_api_panel_sync(panel_id)
    if not p:
        return "⚠️ Panel not found.", InlineKeyboardMarkup([[create_button("Back to Panels", callback_data="adm:api:list", style="danger", icon_custom_emoji_id="5456187398977247949")]])

    if get_panel_type(p) == "augestel":
        try:
            cfg = json.loads(p.get("mapping_json") or "{}")
        except Exception:
            cfg = {}
        status = AUGESTEL_PANEL_STATUS.get(str(panel_id), "Pending")
        text = (
            f"📡 **AUGESTEL PANEL: {escape_md(p['name'])}**\n\n"
            f"🌐 **Login URL:** `{escape_md(cfg.get('login_url', 'N/A'))}`\n"
            f"👤 **Email:** `{escape_md(cfg.get('email', 'N/A'))}`\n"
            f"🔑 **Password:** `******`\n"
            f"⏱️ **Polling Time:** `{p['polling_interval']}s`\n"
            f"📊 **Status:** `{escape_md(status)}`\n"
        )
        buttons = [
            [create_button("Test Connection", callback_data=f"adm:api:test:{panel_id}", style="primary", icon_custom_emoji_id="5258508428212445001")],
            [create_button("Force Re-Login", callback_data=f"adm:api:relogin:{panel_id}", style="success", icon_custom_emoji_id="5244758760429213978")],
            [create_button("Delete Panel", callback_data=f"adm:api:delconf:{panel_id}", style="danger", icon_custom_emoji_id="5422557736330106570")],
            [create_button("Back to Panels", callback_data="adm:api:list", style="primary", icon_custom_emoji_id="5456187398977247949")]
        ]
        return text, InlineKeyboardMarkup(buttons)

    if get_panel_type(p) == "captcha":
        try:
            cfg = json.loads(p.get("mapping_json") or "{}")
        except Exception:
            cfg = {}
        status = CAPTCHA_PANEL_STATUS.get(str(panel_id), "⏳ Pending")
        dt_name = cfg.get('dt_col_name', '') or '(not set)'
        dt_idx = cfg.get('dt_col_idx', 0)
        text = (
            f"🔐 **CAPTCHA PANEL: {escape_md(p['name'])}**\n\n"
            f"🌐 **Login URL:** `{escape_md(cfg.get('login_url', 'N/A'))}`\n"
            f"👤 **Username:** `{escape_md(cfg.get('username', 'N/A'))}`\n"
            f"🔑 **Password:** `******`\n"
            f"📨 **Message Link:** `{escape_md(cfg.get('msg_link', 'N/A'))}`\n"
            f"🔢 **Num Col:** `{escape_md(str(cfg.get('num_col_name', 'N/A')))}` (idx `{cfg.get('num_col_idx', '?')}`)\n"
            f"💬 **Msg Col:** `{escape_md(str(cfg.get('msg_col_name', 'N/A')))}` (idx `{cfg.get('msg_col_idx', '?')}`)\n"
            f"📅 **Date Col:** `{escape_md(str(dt_name))}` (idx `{dt_idx}`)\n"
            f"📊 **Status:** `{escape_md(status)}`\n"
        )
        buttons = [
            [create_button("Test Connection", callback_data=f"adm:api:test:{panel_id}", style="primary", icon_custom_emoji_id="5258508428212445001")],
            [create_button("Force Re-Login", callback_data=f"adm:api:relogin:{panel_id}", style="success", icon_custom_emoji_id="5244758760429213978")],
            [create_button("Delete Panel", callback_data=f"adm:api:delconf:{panel_id}", style="danger", icon_custom_emoji_id="5422557736330106570")],
            [create_button("Back to Panels", callback_data="adm:api:list", style="primary", icon_custom_emoji_id="5456187398977247949")]
        ]
        return text, InlineKeyboardMarkup(buttons)

    masked_token = mask_api_key(p['token'])
    is_custom = bool(p.get("mapping_json"))
    text = (
        f"⚙️ **PANEL DETAILS: {escape_md(p['name'])}**\n\n"
        f"📌 **Panel Name:** {escape_md(p['name'])}\n"
        f"🔗 **Base URL:** `{escape_md(p['url'])}` \n"
        f"🔑 **API Key/Token:** `{escape_md(masked_token)}` \n"
        f"⏱️ **Polling Time:** `{p['polling_interval']}s`\n"
        f"🧩 **Type:** {'🔧 Custom JSON' if is_custom else '📦 Standard'}\n"
    )

    if is_custom:
        try:
            m = json.loads(p["mapping_json"])
            text += "\n🔧 **JSON Path Mapping:**\n"
            labels = {
                "status_path": "Status path",
                "status_value": "Status success value",
                "data_path": "Data array path",
                "num_path": "Number path",
                "msg_path": "Message path",
                "dt_path": "Datetime path",
                "payout_path": "Payout path",
                "cli_path": "Service name path",
            }
            for k, label in labels.items():
                v = m.get(k)
                if v:
                    text += f"• {label}: `{escape_md(str(v))}`\n"
        except Exception:
            pass

    buttons = [
        [create_button("Test Fetch (Debug)", callback_data=f"adm:api:test:{panel_id}", style="primary", icon_custom_emoji_id="5258508428212445001")],
        [create_button("Delete Panel", callback_data=f"adm:api:delconf:{panel_id}", style="danger", icon_custom_emoji_id="5422557736330106570")],
        [create_button("Back to Panels", callback_data="adm:api:list", style="primary", icon_custom_emoji_id="5456187398977247949")]
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_number_quantity_view():
    current_qty = get_setting("number_quantity", "2")
    text = f"🔢 **NUMBER QUANTITY SETTINGS**\n\nSelect how many numbers a user receives per request.\nCurrent setting: `{current_qty}`"
    buttons = [
        [create_button("1", callback_data="adm:setqty:1", style="primary" if current_qty != "1" else "success", icon_custom_emoji_id="5352877703043258544"),
         create_button("2", callback_data="adm:setqty:2", style="primary" if current_qty != "2" else "success", icon_custom_emoji_id="5352877703043258544"),
         create_button("3", callback_data="adm:setqty:3", style="primary" if current_qty != "3" else "success", icon_custom_emoji_id="5352877703043258544")],
        [create_button("4", callback_data="adm:setqty:4", style="primary" if current_qty != "4" else "success", icon_custom_emoji_id="5352877703043258544"),
         create_button("5", callback_data="adm:setqty:5", style="primary" if current_qty != "5" else "success", icon_custom_emoji_id="5352877703043258544"),
         create_button("6", callback_data="adm:setqty:6", style="primary" if current_qty != "6" else "success", icon_custom_emoji_id="5352877703043258544")]
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_force_join_view():
    enabled = is_force_join_enabled()
    chats = get_force_join_chats()
    status = "ENABLED 🟢" if enabled else "DISABLED 🔴"
    text = (
        f"🚪 **FORCE JOIN SETTINGS**\n\n"
        f"📌 **Status:** `{status}`\n\n"
        f"📋 **Channels/Groups:** ({len(chats)})\n"
    )
    if chats:
        for i, ch in enumerate(chats, 1):
            text += (
                f"\n{i}. **{escape_md(ch.get('title', 'N/A'))}** "
                f"[{ch.get('type', 'channel')}]\n"
                f"   ID: `{ch.get('chat_id')}`\n"
                f"   Link: `{escape_md(ch.get('link', 'N/A'))}`\n"
            )
    else:
        text += "_No channels/groups added._\n"
    text += "\n⚠️ **Note:** Bot must be an admin in these channels/groups."

    buttons = [
        [create_button(f"Toggle: {status}", callback_data="adm:fj_toggle", style="success" if enabled else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button("Add Channel/Group", callback_data="adm:fj_add", style="success", icon_custom_emoji_id="5287354223141342798")],
    ]
    if chats:
        buttons.append([create_button("Remove Channel/Group", callback_data="adm:fj_rem_list", style="danger", icon_custom_emoji_id="6267000941547885720")])
    buttons.append([create_button("Back", callback_data="adm:extra_back", style="danger", icon_custom_emoji_id="5456187398977247949")])
    return text, InlineKeyboardMarkup(buttons)


def build_extra_settings_view(user_id: int = 0):
    has_full_extra = (user_id == 0) or has_admin_perm_sync(user_id, "extra")
    has_withdraw = (user_id == 0) or has_admin_perm_sync(user_id, "withdraw_settings")

    text = (
        "⚙️ **EXTRA SETTINGS**\n\n"
        "Select an option to toggle or configure:"
    )

    if not has_full_extra:
        buttons = []
        if has_withdraw:
            buttons.append([create_button("Withdraw Settings", callback_data="adm:w_settings", style="primary", icon_custom_emoji_id="5258096772776991776")])
        return text, InlineKeyboardMarkup(buttons)

    show_msg = get_setting("show_message", "true") == "true"
    show_country_count = get_setting("show_country_count", "false") == "true"
    show_dev = get_setting("show_developer", "true") == "true"
    otp_format = get_setting("otp_group_format", "regular")
    premium_on = (otp_format == "premium")

    msg_status = "ENABLED 🟢" if show_msg else "DISABLED 🔴"
    count_status = "ENABLED 🟢" if show_country_count else "DISABLED 🔴"
    dev_status = "ENABLED 🟢" if show_dev else "DISABLED 🔴"
    otp_format_label = "PREMIUM (Table) 🟢" if premium_on else "REGULAR 🔴"

    buttons = [
        [create_button(f"Show Message: {msg_status}", callback_data="adm:toggle:show_msg", style="success" if show_msg else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button(f"Number Count: {count_status}", callback_data="adm:toggle:country_count", style="success" if show_country_count else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button(f"Show Developer: {dev_status}", callback_data="adm:toggle:show_dev", style="success" if show_dev else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button(f"OTP Group Format: {otp_format_label}", callback_data="adm:toggle:otp_format", style="success" if premium_on else "danger", icon_custom_emoji_id="5258096772776991776")],
        [
            create_button("Refer System", callback_data="adm:refer_settings", style="primary", icon_custom_emoji_id="5258096772776991776"),
            create_button("Force Join Settings", callback_data="adm:fj_settings", style="primary", icon_custom_emoji_id="5258096772776991776"),
        ],
    ]
    if has_withdraw:
        buttons.append([
            create_button("Withdraw Settings", callback_data="adm:w_settings", style="primary", icon_custom_emoji_id="5258096772776991776"),
            create_button("Ranking Bonuses", callback_data="adm:r_bonus_settings", style="primary", icon_custom_emoji_id="5258096772776991776"),
        ])
    else:
        buttons.append([
            create_button("Ranking Bonuses", callback_data="adm:r_bonus_settings", style="primary", icon_custom_emoji_id="5258096772776991776"),
        ])
    buttons.append([create_button("CLI Emojis", callback_data="adm:cliemoji:list", style="primary", icon_custom_emoji_id="5258096772776991776")])
    return text, InlineKeyboardMarkup(buttons)


def build_refer_settings_view():
    refer_on = get_setting("refer_enabled", "true") == "true"
    refer_pct = get_setting("refer_commission_percent", "5")
    refer_status = "ENABLED 🟢" if refer_on else "DISABLED 🔴"

    text = (
        "🎁 **REFER SYSTEM SETTINGS**\n\n"
        f"📌 **Status:** `{refer_status}`\n"
        f"💰 **Commission:** `{refer_pct}%`\n\n"
        "Enable/disable the referral system or update the commission percentage below."
    )
    buttons = [
        [create_button(f"Refer System: {refer_status}", callback_data="adm:toggle:refer", style="success" if refer_on else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button(f"Edit Commission ({refer_pct}%)", callback_data="adm:refer_set_pct", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Back", callback_data="adm:extra_back", style="danger", icon_custom_emoji_id="5456187398977247949")],
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_cli_emojis_view():
    keys = [k for k in SETTINGS_CACHE.keys() if k.startswith("cli_emoji:")]
    text = "🔠 **CLI EMOJI MANAGEMENT**\n\n"
    if keys:
        for k in keys:
            cli = k.split(":", 1)[1]
            text += f"• **{html.escape(cli)}** → `<tg-emoji emoji-id=\"{SETTINGS_CACHE[k]}\">🎲</tg-emoji>`\n"
    else:
        text += "_No CLI emojis configured._\n"

    buttons = [
        [create_button("Add / Edit CLI Emoji", callback_data="adm:cliemoji:add", style="success")],
        [create_button("Delete CLI Emoji", callback_data="adm:cliemoji:del_list", style="danger")],
        [create_button("Back", callback_data="adm:extra_back", style="danger")]
    ]
    return text, InlineKeyboardMarkup(buttons)


@admin_only(perm="extra")
async def admin_cliemoji_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text(
        "Enter the **CLI Name** (e.g., `1xbet`):",
        parse_mode="Markdown"
    )
    return WAIT_CLI_EMOJI_NAME


async def receive_cli_emoji_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    processed = entities_to_tg_emoji(raw, ents)
    clean = strip_all_emojis(processed).lower()
    if not clean:
        await update.message.reply_text("❌ Empty CLI name. Try again:")
        return WAIT_CLI_EMOJI_NAME
    context.user_data['cli_emoji_name'] = clean
    await update.message.reply_text(
        f"CLI: `{escape_md(clean)}`\nNow send the **Premium Emoji** for this CLI:",
        parse_mode="Markdown"
    )
    return WAIT_CLI_EMOJI_VAL


async def receive_cli_emoji_val(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cli_name = context.user_data.get('cli_emoji_name')
    emoji_id = None

    # ১. টেলিগ্রাম এনটিটি থেকে প্রিমিয়াম ইমোজি আইডি খোঁজা
    if update.message.entities:
        for entity in update.message.entities:
            if entity.type == MessageEntity.CUSTOM_EMOJI:
                emoji_id = entity.custom_emoji_id
                break

    # ২. যদি ইউজার সরাসরি <tg-emoji> ট্যাগ পেস্ট করে
    if not emoji_id and update.message.text:
        match = re.search(r'emoji-id="(\d+)"', update.message.text)
        if match:
            emoji_id = match.group(1)

    if emoji_id and cli_name:
        await run_db(set_setting, f"cli_emoji:{cli_name}", emoji_id)
        await update.message.reply_text(f"✅ CLI Emoji for **{escape_md(cli_name)}** saved successfully!", parse_mode="Markdown")
    else:
        await update.message.reply_text("❌ Invalid input. Please send a valid Telegram Premium Emoji.")

    context.user_data.pop('cli_emoji_name', None)
    text_msg, kbd = build_cli_emojis_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


def build_ranking_bonus_settings_view():
    bonus_enabled = get_setting("ranking_bonus_enabled", "true") == "true"
    status_str = "ENABLED 🟢" if bonus_enabled else "DISABLED 🔴"
    b1 = get_setting("rank_bonus_1", "50")
    b2 = get_setting("rank_bonus_2", "30")
    b3 = get_setting("rank_bonus_3", "20")

    text = (
        "🏆 **RANKING BONUS SETTINGS**\n\n"
        f"📌 **Status:** `{status_str}`\n\n"
        f"🥇 **Top 1 Bonus:** `{b1} ৳`\n"
        f"🥈 **Top 2 Bonus:** `{b2} ৳`\n"
        f"🥉 **Top 3 Bonus:** `{b3} ৳`\n"
    )
    buttons = [
        [create_button(f"Ranking Bonus: {status_str}", callback_data="adm:toggle:ranking_bonus", style="success" if bonus_enabled else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button("Edit Top 1 Bonus", callback_data="adm:r_set_b1", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Edit Top 2 Bonus", callback_data="adm:r_set_b2", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Edit Top 3 Bonus", callback_data="adm:r_set_b3", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Back", callback_data="adm:extra_back", style="danger", icon_custom_emoji_id="5456187398977247949")]
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_withdraw_settings_view():
    withdraw_on = get_setting("withdraw_enabled", "true") == "true"
    withdraw_status = "ENABLED 🟢" if withdraw_on else "DISABLED 🔴"
    min_w = get_setting("min_withdraw_amount", "50")
    methods = get_withdraw_methods_sync()

    text = (
        "💳 **WITHDRAW SETTINGS**\n\n"
        f"📌 **Status:** `{withdraw_status}`\n"
        f"💰 **Minimum Withdraw Amount:** `{min_w} ৳`\n\n"
        "📌 **Active Payment Methods:**\n"
    )
    if methods:
        for m in methods:
            text += f"• **{escape_md(m)}**\n"
    else:
        text += "No active payment methods.\n"

    buttons = [
        [create_button(f"Withdraw System: {withdraw_status}", callback_data="adm:toggle:withdraw", style="success" if withdraw_on else "danger", icon_custom_emoji_id="5258096772776991776")],
        [create_button("Add Method", callback_data="adm:w_add_m", style="success", icon_custom_emoji_id="5287354223141342798"),
         create_button("Remove Method", callback_data="adm:w_del_m_list", style="danger", icon_custom_emoji_id="6267000941547885720")],
        [create_button("Edit Min Amount", callback_data="adm:w_set_min", style="primary", icon_custom_emoji_id="5370604433233177619")],
        [create_button("Back", callback_data="adm:extra_back", style="danger", icon_custom_emoji_id="5456187398977247949")]
    ]
    return text, InlineKeyboardMarkup(buttons)


def build_admin_withdraw_requests_view(page: int = 1):
    reqs = get_all_withdraw_requests_sync()

    pending = [r for r in reqs if r["status"] == "pending"]
    others = [r for r in reqs if r["status"] != "pending"]
    pending.sort(key=lambda x: int(x.get("created_at") or 0))
    others.sort(key=lambda x: int(x.get("created_at") or 0), reverse=True)
    reqs = pending + others

    all_uids = list({r["user_id"] for r in reqs})
    uname_map = get_usernames_batch(all_uids)

    per_page = 25
    total_items = len(reqs)
    total_pages = max(1, (total_items + per_page - 1) // per_page)
    if page < 1:
        page = 1
    if page > total_pages:
        page = total_pages

    start_idx = (page - 1) * per_page
    page_reqs = reqs[start_idx:start_idx + per_page]

    pending_count = len(pending)
    text = (
        f"📋 **WITHDRAW REQUESTS (Page {page}/{total_pages})**\n"
        f"Total: `{total_items}`  •  ⏳ Pending: `{pending_count}`\n\n"
        f"📌 Pending shown first (oldest first).\n"
        f"✅❌ Processed shown after (newest first).\n\n"
        "Tap any request to view & manage:"
    )

    buttons = []
    for r in page_reqs:
        if r["status"] == "pending":
            icon_id = None
        elif r["status"] == "approved":
            icon_id = "5424998570539373838"
        else:
            icon_id = "6267000941547885720"

        uname = uname_map.get(r["user_id"]) or r.get("username") or f"User {r['user_id']}"
        uname = uname.lstrip("@")
        if len(uname) > 16:
            uname = uname[:13] + "…"
        
        btn_text = f"@{uname} • {fmt_num(r['amount'])}৳"
        buttons.append([create_button(btn_text, callback_data=f"adm:w_view:{r['id']}", style="primary", icon_custom_emoji_id=icon_id)])

    nav_row = []
    if page > 1:
        nav_row.append(create_button("Prev", callback_data=f"adm:w_page:{page-1}", style="primary", icon_custom_emoji_id="5456187398977247949"))
    if total_pages > 1:
        nav_row.append(create_button(f"{page}/{total_pages}", callback_data="noop", style="primary"))
    if page < total_pages:
        nav_row.append(create_button("Next", callback_data=f"adm:w_page:{page+1}", style="primary"))

    if nav_row:
        buttons.append(nav_row)

    buttons.append([create_button("Back to Panel", callback_data="adm:panel_back", style="danger", icon_custom_emoji_id="5456187398977247949")])
    return text, InlineKeyboardMarkup(buttons)

def build_withdraw_detail_view(req_id: int):
    r = get_withdraw_request_by_id_sync(req_id)
    if not r:
        return "⚠️ Request not found.", InlineKeyboardMarkup([[create_button("Back", callback_data="adm:w_page:1", style="danger", icon_custom_emoji_id="5456187398977247949")]])

    dt_str = datetime.datetime.fromtimestamp(r["created_at"]).strftime("%Y-%m-%d %H:%M:%S") if r["created_at"] else "N/A"
    st_text = r["status"].upper()

    uname_map = get_usernames_batch([r["user_id"]])
    uname = uname_map.get(r["user_id"]) or r.get("username") or f"User {r['user_id']}"
    uname = uname.lstrip("@")
    user_link = f'<a href="tg://user?id={r["user_id"]}">@{html.escape(uname)}</a>'

    text = (
        f"💳 <b>WITHDRAW REQUEST #{r['id']}</b>\n\n"
        f"👤 <b>User:</b> {user_link}\n"
        f"🆔 <b>User ID:</b> <code>{r['user_id']}</code>\n"
        f"📱 <b>Method:</b> <code>{html.escape(str(r['method']))}</code>\n"
        f"💳 <b>Account / Wallet:</b> <code>{html.escape(str(r['wallet_number']))}</code>\n"
        f"💰 <b>Amount:</b> <code>{fmt_num(r['amount'])} ৳</code>\n"
        f"📌 <b>Status:</b> <code>{st_text}</code>\n"
        f"📅 <b>Requested At:</b> <code>{dt_str}</code>\n"
    )
    if r["status"] == "rejected" and r["reject_reason"]:
        text += f"\n❌ <b>Reason:</b>\n<blockquote expandable>{html.escape(r['reject_reason'])}</blockquote>\n"

    buttons = []
    if r["status"] == "pending":
        buttons.append([
            create_button("APPROVE", callback_data=f"adm:w_app:{r['id']}", style="success", icon_custom_emoji_id="5424998570539373838"),
            create_button("REJECT", callback_data=f"adm:w_rej_start:{r['id']}", style="danger", icon_custom_emoji_id="6267000941547885720")
        ])
    buttons.append([create_button("Back to Requests", callback_data="adm:w_page:1", style="primary", icon_custom_emoji_id="5456187398977247949")])

    return text, InlineKeyboardMarkup(buttons)


def build_allocation_keyboard(service: str, country: str, numbers: list, hide_cc: bool = False):
    otp_group_link = clean_tg_link(get_setting("otp_group_link", "https://t.me/your_otp_group"))
    buttons = []
    srv_cb = _cb_clean(service)
    cnt_cb = _cb_clean(country)

    cc_len_str = get_setting(f"cc_len:{service}:{country}", "0")
    try:
        cc_len = int(cc_len_str)
    except ValueError:
        cc_len = 0

    display_numbers = []
    for num in numbers:
        if hide_cc and cc_len > 0:
            display_numbers.append(num[cc_len:] if len(num) > cc_len else num)
        else:
            display_numbers.append(num)

    for num in display_numbers:
        buttons.append([create_button(f"{num}", copy_text=str(num), style="success")])

    if cc_len > 0:
        if hide_cc:
            toggle_text = "Show CC"
            toggle_data = f"togcc:{srv_cb}:{cnt_cb}:0"
            toggle_emoji = "6156854417887859761"
        else:
            toggle_text = "Hide CC"
            toggle_data = f"togcc:{srv_cb}:{cnt_cb}:1"
            toggle_emoji = "5337166274587799243"
        buttons.append([create_button(toggle_text, callback_data=toggle_data, style="danger", icon_custom_emoji_id=toggle_emoji)])

    buttons.append([
        create_button("Change All", callback_data=f"chg:{srv_cb}:{cnt_cb}", style="primary", icon_custom_emoji_id="5219934485113493317"),
        create_button("OTP Group", url=otp_group_link, style="primary", icon_custom_emoji_id="5836754611305713785")
    ])
    buttons.append([create_button("Back", callback_data=f"srv_{srv_cb}", style="danger", icon_custom_emoji_id="5456187398977247949")])
    return InlineKeyboardMarkup(buttons)

def get_services_keyboard():
    services = [s for s in SERVICES_CACHE.keys() if get_active_countries_for_service(s)]
    if not services:
        return None, "No services currently available."

    buttons = []
    for i in range(0, len(services), 2):
        row = []
        row.append(create_button(services[i], callback_data=f"srv_{_cb_clean(services[i])}", style="primary"))
        if i + 1 < len(services):
            row.append(create_button(services[i+1], callback_data=f"srv_{_cb_clean(services[i+1])}", style="primary"))
        buttons.append(row)

    return InlineKeyboardMarkup(buttons), '<tg-emoji emoji-id="5352922460897452503">📍</tg-emoji> Please select a service:'

flask_app = Flask(__name__)


@flask_app.route('/')
def home():
    return f"Bot running! DB Mode: {CURRENT_DB_MODE}"


@flask_app.route('/health')
def health():
    return jsonify({
        "status": "ok",
        "db_mode": CURRENT_DB_MODE,
        "known_users": len(KNOWN_USERS),
        "services": len(SERVICES_CACHE),
        "panels": len(PANEL_TASKS),
        "captcha_sessions": len(CAPTCHA_SESSIONS),
        "augestel_sessions": len(AUGESTEL_SESSIONS),
        "batch_rpc": "enabled" if _BATCH_RPC_AVAILABLE else "fallback",
        "firebase": "connected" if firebase_db_ref else "disabled",
        "otp_retention_days": OTP_ID_RETENTION_SECONDS // 86400,
        "send_concurrency": SEND_CONCURRENCY,
        "chat_locks": len(_CHAT_LOCKS),
        "force_join_enabled": is_force_join_enabled(),
        "refer_enabled": get_setting("refer_enabled", "true") == "true",
        "otp_group_format": get_setting("otp_group_format", "regular"),
        "anti_abuse": {
            "cooldown_seconds": NUMBER_CLAIM_COOLDOWN,
            "change_window_seconds": NUMBER_CHANGE_WINDOW,
            "ban_threshold": NUMBER_CHANGE_BAN_THRESHOLD,
            "active_cooldowns": len(_LAST_NUMBER_CLAIM),
            "tracked_changes": len(_RECENT_NUMBER_CHANGES),
            "in_memory_bans": len(_IN_MEMORY_BANNED),
        },
    })


def run_flask():
    port = int(os.environ.get("PORT", 8080))
    flask_app.run(host="0.0.0.0", port=port, threaded=True)


(
    ADD_SERVICE, ADD_COUNTRY, WAIT_PAYOUT_AMOUNT, ADD_NUMBERS,
    WAIT_CHANNEL, WAIT_SUPPORT, WAIT_OTP_LINK, WAIT_OTP_GROUP_ID,
    WAIT_BROADCAST_MSG, WAIT_PANEL_NAME, WAIT_PANEL_URL, WAIT_PANEL_TOKEN,
    WAIT_PANEL_INTERVAL, WAIT_ADMIN_ID, WAIT_ADMIN_NAME,
    WAIT_WITHDRAW_WALLET, WAIT_WITHDRAW_AMOUNT, WAIT_NEW_WITHDRAW_METHOD,
    WAIT_MIN_WITHDRAW_AMOUNT, WAIT_REJECT_REASON, WAIT_DEV_NAME,
    WAIT_DEV_LINK, WAIT_RANK1_BONUS, WAIT_RANK2_BONUS, WAIT_RANK3_BONUS,
    WAIT_MAP_STATUS_PATH, WAIT_MAP_STATUS_VALUE, WAIT_MAP_DATA_PATH,
    WAIT_MAP_NUM_PATH, WAIT_MAP_MSG_PATH, WAIT_MAP_DT_PATH,
    WAIT_MAP_PAYOUT_PATH, WAIT_MAP_CLI_PATH,
    WAIT_CPT_LOGIN_URL, WAIT_CPT_USERNAME, WAIT_CPT_PASSWORD,
    WAIT_CPT_MSG_LINK, WAIT_CPT_NUM_COL_NAME, WAIT_CPT_NUM_COL_IDX,
    WAIT_CPT_MSG_COL_NAME, WAIT_CPT_MSG_COL_IDX,
    WAIT_CPT_DT_COL_NAME, WAIT_CPT_DT_COL_IDX,
    WAIT_FJ_CHAT_ID, WAIT_FJ_CHAT_TITLE, WAIT_FJ_CHAT_LINK, WAIT_FJ_CHAT_TYPE,
    WAIT_REFER_PERCENT,
    WAIT_CC_LENGTH,
    WAIT_USER_SEARCH,
    WAIT_COUNTRY_SHORT,
    WAIT_CLI_EMOJI_NAME, WAIT_CLI_EMOJI_VAL,
    WAIT_AUG_EMAIL, WAIT_AUG_PASSWORD, WAIT_AUG_API_KEY,
    WAIT_EDIT_SERVICE_NAME, WAIT_EDIT_COUNTRY_NAME, WAIT_EDIT_COUNTRY_SHORT,
    WAIT_AUTOBAN_THRESHOLD, WAIT_AUTOBAN_WINDOW,
    WAIT_AUTOBAN_INACTIVE_DAYS, WAIT_AUTOBAN_INACTIVE_OTPS,
) = range(63)


def get_main_keyboard(user_id: int):
    buttons = [
        [KeyboardButton("Get Number", icon_custom_emoji_id="6204108584381322968", style="success")],
        [
            KeyboardButton("Profile", icon_custom_emoji_id="6307589808424228455", style="primary"),
            KeyboardButton("Wallet", icon_custom_emoji_id="6206155797722830770", style="primary")
        ],
        [
            KeyboardButton("Ranking", icon_custom_emoji_id="6206343625232619150", style="danger"),
            KeyboardButton("Support", icon_custom_emoji_id="5348323259593014362", style="danger")
        ]
    ]
    if is_admin_sync(user_id):
        buttons.append([KeyboardButton("Admin Panel", icon_custom_emoji_id="5258508428212445001", style="danger")])
    return ReplyKeyboardMarkup(buttons, resize_keyboard=True)


def get_admin_keyboard(use_premium: Optional[bool] = None, user_id: int = 0):
    premium = _is_premium_emojis_enabled(use_premium)
    if user_id:
        can_srv = has_admin_perm_sync(user_id, "services")
        can_bc = has_admin_perm_sync(user_id, "broadcast")
        can_um = has_admin_perm_sync(user_id, "users") or has_admin_perm_sync(user_id, "admins")
        can_pay = has_admin_perm_sync(user_id, "payouts")
        can_live = has_admin_perm_sync(user_id, "live_receivers")
        can_gs = has_any_global_settings_perm(user_id)
    else:
        can_srv = can_bc = can_um = can_pay = can_live = can_gs = True

    candidates = []
    if can_srv:
        candidates.append(
            KeyboardButton("Services", icon_custom_emoji_id="5258096772776991776", style="success")
            if premium else KeyboardButton("🏷️ Services", style="success")
        )
    if can_bc:
        candidates.append(
            KeyboardButton("Broadcast", icon_custom_emoji_id="5800920921766104807", style="success")
            if premium else KeyboardButton("📢 Broadcast", style="success")
        )
    if can_um:
        candidates.append(
            KeyboardButton("User Manager", icon_custom_emoji_id="6307589808424228455", style="primary")
            if premium else KeyboardButton("👥 User Manager", style="primary")
        )
    if can_pay:
        candidates.append(
            KeyboardButton("Manage Payouts", icon_custom_emoji_id="5417924076503062111", style="primary")
            if premium else KeyboardButton("💰 Manage Payouts", style="primary")
        )
    if can_live:
        candidates.append(
            KeyboardButton("Live Receivers", icon_custom_emoji_id="5352877703043258544", style="primary")
            if premium else KeyboardButton("📡 Live Receivers", style="primary")
        )
    if can_gs:
        candidates.append(
            KeyboardButton("Global Settings", icon_custom_emoji_id="5258096772776991776", style="primary")
            if premium else KeyboardButton("⚙️ Global Settings", style="primary")
        )

    buttons = [candidates[i:i + 2] for i in range(0, len(candidates), 2)]
    buttons.append([
        KeyboardButton("Back", icon_custom_emoji_id="5456187398977247949", style="danger")
        if premium else KeyboardButton("◀️ Back", style="danger")
    ])
    return ReplyKeyboardMarkup(buttons, resize_keyboard=True)


def get_global_settings_keyboard(user_id: int = 0):
    if user_id:
        can_links = has_admin_perm_sync(user_id, "links")
        can_api = has_admin_perm_sync(user_id, "api")
        can_qty = has_admin_perm_sync(user_id, "number_qty")
        can_extra = has_admin_perm_sync(user_id, "extra") or has_admin_perm_sync(user_id, "withdraw_settings")
    else:
        can_links = can_api = can_qty = can_extra = True

    candidates = []
    if can_links:
        candidates.append(KeyboardButton("Edit Links", icon_custom_emoji_id="5370604433233177619", style="success"))
    if can_api:
        candidates.append(KeyboardButton("Edit API", icon_custom_emoji_id="5258096772776991776", style="success"))
    if can_qty:
        candidates.append(KeyboardButton("Number Quantity", icon_custom_emoji_id="5352877703043258544", style="primary"))
    if can_extra:
        candidates.append(KeyboardButton("Extra", icon_custom_emoji_id="5258096772776991776", style="primary"))

    buttons = [candidates[i:i + 2] for i in range(0, len(candidates), 2)]
    buttons.append([KeyboardButton("Back", icon_custom_emoji_id="5456187398977247949", style="danger")])
    return ReplyKeyboardMarkup(buttons, resize_keyboard=True)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    first_name = update.effective_user.first_name or ""
    username = update.effective_user.username or ""
    await run_db(save_user, user_id, first_name, username)

    if not is_admin_sync(user_id) and await run_db(is_user_banned_sync, user_id):
        await update.message.reply_text(
            BANNED_TEXT, reply_markup=_banned_keyboard(), parse_mode="HTML",
        )
        return

    if context.args:
        try:
            ref_arg = (context.args[0] or "").strip()
            if ref_arg.isdigit():
                referrer_id = int(ref_arg)
                if referrer_id != user_id and referrer_id > 0:
                    await run_db(set_user_referrer_sync, user_id, referrer_id)
        except Exception as e:
            logger.warning(f"start refer arg error: {e}")

    for key in ('service_name', 'country_name', 'w_method', 'w_wallet',
                'reject_req_id', 'new_api_name', 'new_api_url', 'new_api_token',
                'new_admin_id', 'pay_edit_service', 'pay_edit_country', 'pay_flow',
                'payout_amount', 'panel_flow', 'map_status_path', 'map_status_value',
                'map_data_path', 'map_num_path', 'map_msg_path', 'map_dt_path',
                'map_payout_path', 'map_cli_path', 'new_api_interval',
                'cpt_login_url', 'cpt_username', 'cpt_password', 'cpt_msg_link',
                'cpt_num_col_name', 'cpt_num_col_idx', 'cpt_msg_col_name',
                'fj_chat_id', 'fj_chat_title', 'fj_chat_link', 'cc_length', 'aug_email', 'aug_password',
                'country_short', 'edit_old_service', 'edit_srv', 'edit_old_country',
                'edit_new_country', 'add_numbers_return_country'):
        context.user_data.pop(key, None)

    context.user_data['current_menu'] = 'main'

    if not is_admin_sync(user_id) and is_force_join_enabled():
        chats = get_force_join_chats()
        if chats:
            ok = await is_user_force_join_ok(context.bot, user_id, use_cache=False)
            if not ok:
                await update.message.reply_text(
                    FORCE_JOIN_TEXT,
                    reply_markup=build_force_join_keyboard(chats),
                    parse_mode="HTML",
                    link_preview_options=LinkPreviewOptions(is_disabled=True),
                )
                return

    first_name_esc = escape_md(first_name or "User")
    msg = f"Welcome, {first_name_esc}!\nPlease select an option from the menu:"
    await update.message.reply_text(msg, reply_markup=get_main_keyboard(user_id), parse_mode="Markdown")


async def handle_text_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text
    user_id = update.effective_user.id
    first_name = update.effective_user.first_name or ""
    username = update.effective_user.username or ""
    await run_db(save_user, user_id, first_name, username)

    text_upper = _clean_menu_text(text).upper()
    user_is_admin = is_admin_sync(user_id)

    if not user_is_admin and text_upper in ("GET NUMBER",):
        if await run_db(is_user_banned_sync, user_id):
            await update.message.reply_text(
                BANNED_TEXT, reply_markup=_banned_keyboard(), parse_mode="HTML",
            )
            return

    if not user_is_admin and is_force_join_enabled():
        chats = get_force_join_chats()
        if chats:
            ok = await is_user_force_join_ok(context.bot, user_id)
            if not ok:
                await update.message.reply_text(
                    FORCE_JOIN_TEXT,
                    reply_markup=build_force_join_keyboard(chats),
                    parse_mode="HTML",
                    link_preview_options=LinkPreviewOptions(is_disabled=True),
                )
                return

    if text_upper == "GET NUMBER":
        kbd, msg = get_services_keyboard()
        if not kbd:
            await update.message.reply_text(msg)
        else:
            await update.message.reply_text(msg, reply_markup=kbd, parse_mode="HTML")

    elif text_upper == "PROFILE":
        first_name_esc = escape_md(first_name or "User")
        bot_username = context.bot.username or "bot"
        refer_link = f"https://t.me/{bot_username}?start={user_id}"

        prof = await run_db(get_user_profile_sync, user_id)
        bal_str = fmt_num(prof["balance"])
        today_str = fmt_num(prof["today_earned"])
        total_str = fmt_num(prof["total_earned"])
        refer_str = fmt_num(prof["refer_earned"])
        total_otps = prof["total_otps"]

        profile_text = (
            "👤 **USER PROFILE**\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            f"📝 Name: {first_name_esc}\n"
            f"🆔 ID: `{user_id}`\n"
            f"💰 Balance: {bal_str} ৳\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            f"🎯 Today's Earn: {today_str} ৳\n"
            f"📈 Total Earned: {total_str} ৳\n"
            f"👥 Earned from Refer: {refer_str} ৳\n"
            f"📨 Total OTPs: {total_otps}\n"
            "━━━━━━━━━━━━━━━━━━━━"
        )
        kbd = InlineKeyboardMarkup([[create_button("Referral Link", copy_text=refer_link, style="success")]])
        await update.message.reply_text(profile_text, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper == "WALLET":
        bal = await run_db(get_user_balance_sync, user_id)
        bal_str = fmt_num(bal)
        wallet_text = (
            f"👛 **YOUR WALLET**\n\n"
            f"🆔 **User ID:** `{user_id}`\n"
            f"💰 **Balance:** `{bal_str} ৳`"
        )
        kbd = InlineKeyboardMarkup([[create_button("💸 Withdraw", callback_data="usr:withdraw", style="success")]])
        await update.message.reply_text(wallet_text, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper in ["RANKING", "LEADERBOARD"]:
        leaderboard_msg = await run_db(get_ranking_leaderboard_sync, user_id)
        await update.message.reply_text(leaderboard_msg, parse_mode="HTML", link_preview_options=LinkPreviewOptions(is_disabled=True))

    elif text_upper == "SUPPORT":
        sp_link = clean_tg_link(get_setting("support", "@your_support"))
        ch_link = clean_tg_link(get_setting("channel", "https://t.me/your_channel"))
        kbd = InlineKeyboardMarkup([
            [create_button("Support", url=sp_link, style="primary"),
             create_button("Channel", url=ch_link, style="primary")]
        ])
        await update.message.reply_text("Click below to contact support or join our channel:", reply_markup=kbd)

    elif text_upper == "ADMIN PANEL" and user_is_admin:
        context.user_data['current_menu'] = 'admin'
        total_users = len(await run_db(get_all_users))
        role_lbl = get_admin_role_label(user_id)
        panel_text = (
            f"**ADMIN PANEL**\n\n"
            f"🎭 Role: **{role_lbl}**\n"
            f"⚙️ DB Mode: **{CURRENT_DB_MODE}**\n"
            f"👥 Total Registered Users: `{total_users}`"
        )
        await _reply_with_emoji_fallback(
            update.message,
            lambda prem: (panel_text, get_admin_keyboard(use_premium=prem, user_id=user_id)),
            parse_mode="Markdown",
        )

    elif (text_upper == "MANAGE PAYOUTS" or text_upper == "WITHDRAW") and user_is_admin:
        if not has_admin_perm_sync(user_id, "payouts"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Manage Payouts.")
            return
        context.user_data['current_menu'] = 'admin'
        text_msg, kbd = await run_db(build_admin_withdraw_requests_view, 1)
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper == "SERVICES" and user_is_admin:
        if not has_admin_perm_sync(user_id, "services"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Services Control.")
            return
        context.user_data['current_menu'] = 'admin'
        text_msg, kbd = await run_db(build_admin_services_view)
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="HTML")

    elif text_upper == "USER MANAGER" and user_is_admin:
        if not (has_admin_perm_sync(user_id, "users") or has_admin_perm_sync(user_id, "admins")):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for User Manager.")
            return
        context.user_data['current_menu'] = 'admin'
        await _reply_with_emoji_fallback(
            update.message,
            lambda prem: build_user_manager_view(use_premium=prem, user_id=user_id),
            parse_mode="Markdown",
        )

    elif text_upper == "LIVE RECEIVERS" and user_is_admin:
        if not has_admin_perm_sync(user_id, "live_receivers"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Live Receivers.")
            return
        context.user_data['current_menu'] = 'admin'
        live_events = await run_db(get_live_receiver_events_sync, "all")
        await _reply_with_emoji_fallback(
            update.message,
            lambda prem: build_live_receivers_view("all", 1, use_premium=prem, events=live_events),
            parse_mode="HTML",
            link_preview_options=LinkPreviewOptions(is_disabled=True),
        )

    elif text_upper == "GLOBAL SETTINGS" and user_is_admin:
        if not has_any_global_settings_perm(user_id):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Global Settings.")
            return
        context.user_data['current_menu'] = 'global_settings'
        await update.message.reply_text(
            "⚙️ **GLOBAL SETTINGS MENU**\n\nSelect an option from below keyboard:",
            reply_markup=get_global_settings_keyboard(user_id=user_id), parse_mode="Markdown"
        )

    elif text_upper == "EDIT LINKS" and user_is_admin:
        if not has_admin_perm_sync(user_id, "links"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Links Control.")
            return
        context.user_data['current_menu'] = 'global_settings'
        text_msg, kbd = build_edit_links_view()
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper == "EDIT API" and user_is_admin:
        if not has_admin_perm_sync(user_id, "api"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for API Control.")
            return
        context.user_data['current_menu'] = 'global_settings'
        text_msg, kbd = await run_db(build_api_panels_view)
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper == "NUMBER QUANTITY" and user_is_admin:
        if not has_admin_perm_sync(user_id, "number_qty"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Number Quality Control.")
            return
        context.user_data['current_menu'] = 'global_settings'
        text_msg, kbd = build_number_quantity_view()
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper == "EXTRA" and user_is_admin:
        if not (has_admin_perm_sync(user_id, "extra") or has_admin_perm_sync(user_id, "withdraw_settings")):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Extra Settings.")
            return
        context.user_data['current_menu'] = 'global_settings'
        text_msg, kbd = build_extra_settings_view(user_id=user_id)
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif text_upper == "ADMIN CONTROL" and user_is_admin:
        if not has_admin_perm_sync(user_id, "admins"):
            await update.message.reply_text("⛔ Unauthorized! You do not have permission for Admin Control.")
            return
        context.user_data['current_menu'] = 'admin'
        await run_db(get_all_admins_sync)
        await _reply_with_emoji_fallback(
            update.message,
            lambda prem: build_admin_control_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif text_upper == "BACK":
        curr_menu = context.user_data.get('current_menu', 'main')
        if curr_menu == 'global_settings' and user_is_admin:
            context.user_data['current_menu'] = 'admin'
            total_users = len(await run_db(get_all_users))
            role_lbl = get_admin_role_label(user_id)
            panel_text = (
                f"**ADMIN PANEL**\n\n"
                f"🎭 Role: **{role_lbl}**\n"
                f"⚙️ DB Mode: **{CURRENT_DB_MODE}**\n"
                f"👥 Total Registered Users: `{total_users}`"
            )
            await _reply_with_emoji_fallback(
                update.message,
                lambda prem: (panel_text, get_admin_keyboard(use_premium=prem, user_id=user_id)),
                parse_mode="Markdown",
            )
        else:
            context.user_data['current_menu'] = 'main'
            await update.message.reply_text("Main Menu", reply_markup=get_main_keyboard(user_id))


async def user_start_withdraw_flow(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()

    user_id = query.from_user.id

    if not is_admin_sync(user_id) and await run_db(is_user_banned_sync, user_id):
        await query.edit_message_text(
            "🚫 You are banned and cannot withdraw.\n\nContact support to resolve.",
            reply_markup=_banned_keyboard(), parse_mode="HTML",
        )
        return ConversationHandler.END

    withdraw_on = get_setting("withdraw_enabled", "true") == "true"
    if not withdraw_on:
        await query.edit_message_text("❌ Withdraw system is currently disabled by Admin.")
        return ConversationHandler.END

    method = query.data.split(":", 2)[2]

    bal = await run_db(get_user_balance_sync, user_id)
    min_w = float(get_setting("min_withdraw_amount", "50") or 50)

    if bal < min_w:
        await query.edit_message_text(f"❌ Minimum withdraw amount is `{fmt_num(min_w)} ৳`.\nYour current balance is `{fmt_num(bal)} ৳`.", parse_mode="Markdown")
        return ConversationHandler.END

    context.user_data['w_method'] = method
    await query.edit_message_text(f"Please enter your **{escape_md(method)}** account number / wallet address:", parse_mode="Markdown")
    return WAIT_WITHDRAW_WALLET


async def receive_withdraw_wallet(update: Update, context: ContextTypes.DEFAULT_TYPE):
    wallet_no = update.message.text.strip()
    user_id = update.effective_user.id
    method = context.user_data.get('w_method', '')

    method_lower = method.lower()
    is_valid = True
    error_msg = ""

    if any(m in method_lower for m in ['bkash', 'nagad', 'rocket', 'upay', 'cellfin']):
        clean_num = re.sub(r'\D', '', wallet_no)
        if len(clean_num) < 11:
            is_valid = False
            error_msg = "❌ Invalid Account Number! Mobile banking numbers must be at least 11 digits."
    elif any(m in method_lower for m in ['trc', 'usdt', 'crypto', 'wallet']):
        if len(wallet_no) < 30 or not wallet_no.isalnum():
            is_valid = False
            error_msg = "❌ Invalid Wallet Address! Please enter a valid Crypto/TRC20 wallet address."
    else:
        if len(wallet_no) < 8:
            is_valid = False
            error_msg = "❌ Invalid Details! Account / Wallet address must be at least 8 characters long."

    if not is_valid:
        await update.message.reply_text(f"{error_msg}\n\nPlease enter a valid **{escape_md(method)}** account number / wallet address again:", parse_mode="Markdown")
        return WAIT_WITHDRAW_WALLET

    context.user_data['w_wallet'] = wallet_no
    bal = await run_db(get_user_balance_sync, user_id)
    min_w = float(get_setting("min_withdraw_amount", "50") or 50)

    await update.message.reply_text(
        f"Selected Method: **{escape_md(method)}**\n"
        f"Wallet/Account: `{escape_md(wallet_no)}` \n\n"
        f"Enter withdraw amount:\n"
        f"📌 Minimum Amount: `{fmt_num(min_w)} ৳`\n"
        f"💰 Available Balance: `{fmt_num(bal)} ৳`",
        parse_mode="Markdown"
    )
    return WAIT_WITHDRAW_AMOUNT


async def receive_withdraw_amount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    username = update.effective_user.username or ""
    input_text = update.message.text.strip()

    try:
        amount = float(input_text)
    except ValueError:
        await update.message.reply_text("❌ Invalid amount! Please enter numbers only.\nType /cancel to abort.")
        return WAIT_WITHDRAW_AMOUNT

    bal = await run_db(get_user_balance_sync, user_id)
    min_w = float(get_setting("min_withdraw_amount", "50") or 50)

    if amount < min_w:
        await update.message.reply_text(f"❌ Amount cannot be less than minimum withdraw limit (`{fmt_num(min_w)} ৳`).\nPlease enter again:")
        return WAIT_WITHDRAW_AMOUNT

    if amount > bal:
        await update.message.reply_text(f"❌ Insufficient balance! Your available balance is `{fmt_num(bal)} ৳`.\nPlease enter again:")
        return WAIT_WITHDRAW_AMOUNT

    method = context.user_data.get('w_method')
    wallet_no = context.user_data.get('w_wallet')

    success = await run_db(deduct_user_balance_sync, user_id, amount)
    if not success:
        await update.message.reply_text("❌ Failed to process withdraw. Insufficient balance.")
        context.user_data.pop('w_method', None)
        context.user_data.pop('w_wallet', None)
        return ConversationHandler.END

    req_id = await run_db(create_withdraw_request_sync, user_id, method, wallet_no, amount, username)

    if not req_id:
        await run_db(refund_user_balance_sync, user_id, amount)
        await update.message.reply_text("❌ Failed to create withdraw request. Amount refunded to your wallet.")
        context.user_data.pop('w_method', None)
        context.user_data.pop('w_wallet', None)
        return ConversationHandler.END

    success_msg = (
        "✅ **WITHDRAWAL REQUEST SUBMITTED**\n\n"
        f"📌 **Request ID:** `#{req_id}`\n"
        f"📱 **Method:** `{escape_md(method)}` \n"
        f"💳 **Account:** `{escape_md(wallet_no)}` \n"
        f"💰 **Amount:** `{fmt_num(amount)} ৳`\n\n"
        "Your request has been submitted to Admin for approval."
    )
    await update.message.reply_text(success_msg, parse_mode="Markdown")

    context.user_data.pop('w_method', None)
    context.user_data.pop('w_wallet', None)
    return ConversationHandler.END


@admin_only(perm="payouts")
async def start_edit_payout(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    parts = query.data.split(":", 4)
    if len(parts) < 5:
        await query.message.reply_text("⚠️ Invalid edit request.")
        return ConversationHandler.END
    service = _resolve_full_key(parts[3], list(SERVICES_CACHE.keys()))
    country = _resolve_full_key(parts[4], list(SERVICES_CACHE.get(service, {}).keys()))
    context.user_data['pay_edit_service'] = service
    context.user_data['pay_edit_country'] = country
    context.user_data['pay_flow'] = 'edit'

    curr = get_payout_sync(service, country)
    await query.message.reply_text(
        f"💰 Editing payout for:\n"
        f"🏷️ Service: <b>{safe_html_escape(service)}</b>\n"
        f"🏳️ Country: <b>{safe_html_escape(country)}</b>\n\n"
        f"Current payout: <code>{fmt_num(curr)} ৳</code>\n"
        f"Send new amount (or send <code>default</code> for {fmt_num(DEFAULT_PAYOUT)} ৳):",
        parse_mode="HTML"
    )
    return WAIT_PAYOUT_AMOUNT


async def receive_payout_amount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    input_text = update.message.text.strip().lower()
    if input_text in ("default", "d", ""):
        val = DEFAULT_PAYOUT
    else:
        try:
            val = float(input_text)
            if val < 0:
                val = 0.0
        except ValueError:
            await update.message.reply_text("❌ Invalid amount! Please enter a valid number (e.g., 0.5, 1, 2.5) or `default`.")
            return WAIT_PAYOUT_AMOUNT

    flow = context.user_data.get('pay_flow')

    if flow in ('edit', 'country_edit'):
        service = context.user_data.get('pay_edit_service')
        country = context.user_data.get('pay_edit_country')
        await run_db(set_payout_sync, service, country, val)
        await update.message.reply_text(
            f"✅ Payout for <b>{safe_html_escape(service)}</b> → "
            f"<b>{safe_html_escape(country)}</b> set to <code>{fmt_num(val)} ৳</code>!",
            parse_mode="HTML"
        )
        if flow == 'country_edit':
            text_msg, kbd = build_country_edit_view(service, country)
        else:
            text_msg, kbd = build_payout_manage_view(service)
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="HTML")
        for key in ('pay_flow', 'pay_edit_service', 'pay_edit_country'):
            context.user_data.pop(key, None)
        return ConversationHandler.END
    else:
        context.user_data['payout_amount'] = val
        await update.message.reply_text(
            f"✅ Payout set to `{fmt_num(val)} ৳` per OTP.\n\n"
            "Enter the **Country Code Length** (how many digits at the start of the number is the country code, e.g., `1` for US, `2` for BD, `3` for others).\n"
            "Send `0` if you don't want to hide any country code.",
            parse_mode="Markdown"
        )
        return WAIT_CC_LENGTH


async def receive_cc_length(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val.isdigit():
        await update.message.reply_text("❌ Please enter a valid number (e.g., 0, 1, 2, 3):")
        return WAIT_CC_LENGTH
    cc_len = int(val)
    context.user_data['cc_length'] = cc_len

    service = context.user_data.get('service_name')
    country = context.user_data.get('country_name')
    if service and country:
        await run_db(set_setting, f"cc_len:{service}:{country}", str(cc_len))

    await update.message.reply_text(
        f"✅ CC Length set to `{cc_len}` digits.\n\n"
        "Now send the numbers (as a text file or one number per line):",
        parse_mode="Markdown"
    )
    return ADD_NUMBERS


def _build_user_detail_view(
    uid: int,
    user_data: dict,
    back_cb: str = "adm:usr:control",
    refer_count: Optional[int] = None,
) -> Tuple[str, InlineKeyboardMarkup]:
    uname = user_data.get("username") or "No username"
    fname = user_data.get("first_name") or "No name"
    balance = fmt_num(user_data.get("balance", 0))
    today = fmt_num(user_data.get("today_earned", 0))
    total_e = fmt_num(user_data.get("total_earned", 0))
    ref_e = fmt_num(user_data.get("refer_earned", 0))
    total_o = int(user_data.get("total_otps") or 0)
    weekly_o = int(user_data.get("weekly_otps") or 0)
    ref_by = user_data.get("referred_by") or "None"
    last_date = user_data.get("last_earn_date") or "N/A"
    if refer_count is None:
        refer_count = get_user_refer_count_sync(uid)

    is_banned = bool(user_data.get("is_banned", False)) or (uid in _IN_MEMORY_BANNED)
    ban_reason = ""
    if is_banned:
        ban_reason = _IN_MEMORY_BAN_REASONS.get(uid) or user_data.get("ban_reason") or ""

    status_icon = "🚫 <b>BANNED</b>" if is_banned else "✅ Active"
    back_tok = _encode_usr_back(back_cb)

    text = (
        f"👤 <b>USER DETAILS</b>\n\n"
        f"👤 <b>Name:</b> {html.escape(fname)}\n"
        f"🆔 <b>User ID:</b> <code>{uid}</code>\n"
        f"🏷️ <b>Username:</b> @{html.escape(uname)}\n"
        f"📊 <b>Status:</b> {status_icon}\n"
        f"💰 <b>Balance:</b> <code>{balance} ৳</code>\n"
        f"📈 <b>Lifetime Earnings:</b> <code>{total_e} ৳</code> (<code>{total_o} OTPs</code>)\n"
        f"📅 <b>Today Earned:</b> <code>{today} ৳</code>\n"
        f"👥 <b>Total Refers:</b> <code>{refer_count}</code>\n"
        f"🎁 <b>Earned from Refer:</b> <code>{ref_e} ৳</code>\n"
        f"🔗 <b>Referred By:</b> <code>{ref_by}</code>\n"
        f"📊 <b>Last Week OTPs:</b> <code>{weekly_o} OTPs</code>\n"
        f"📅 <b>Last Earn Date:</b> <code>{html.escape(str(last_date))}</code>"
    )
    if is_banned and ban_reason:
        text += f"\n\n🚫 <b>Ban Reason:</b>\n<blockquote>{html.escape(ban_reason)}</blockquote>"

    buttons = []
    if is_banned:
        buttons.append([create_button("🔓 Unban User", callback_data=f"adm:usr:unban:{uid}:{back_tok}", style="success")])
    else:
        buttons.append([create_button("🚫 Ban User", callback_data=f"adm:usr:ban:{uid}:{back_tok}", style="danger")])
    buttons.append([create_button("🗑️ Release All Numbers", callback_data=f"adm:usr:release:{uid}:{back_tok}", style="danger")])
    if back_cb == "adm:usr:control":
        buttons.append([create_button("🔍 Search Another", callback_data="adm:usr:search", style="primary")])
    buttons.append([create_button("Back", callback_data=back_cb, style="primary")])

    return text, InlineKeyboardMarkup(buttons)


@admin_only(perm="users")
async def admin_search_user_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text(
        "🔍 **SEARCH USER**\n\n"
        "Send me the **User ID** or **Username** (with or without @) of the user you want to find.",
        parse_mode="Markdown"
    )
    return WAIT_USER_SEARCH


async def receive_user_search(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query_text = update.message.text.strip()
    user_data = await run_db(search_user_sync, query_text)

    if not user_data:
        await update.message.reply_text(
            f"❌ User `{escape_md(query_text)}` not found.\nTry another ID/Username or type /cancel.",
            parse_mode="Markdown",
        )
        return WAIT_USER_SEARCH

    uid = int(user_data.get("user_id"))
    refer_count = await run_db(get_user_refer_count_sync, uid)
    text, kbd = _build_user_detail_view(uid, user_data, back_cb="adm:usr:control", refer_count=refer_count)
    await update.message.reply_text(text, reply_markup=kbd, parse_mode="HTML")
    return ConversationHandler.END


@admin_only(perm="users")
async def admin_autoban_thresh_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    curr = get_abuse_ban_threshold()
    await update.callback_query.message.reply_text(
        f"🔁 **MAX NUMBER CHANGES LIMIT**\n\nCurrent limit: `{curr}` changes\nSend new max number changes (e.g., `3`), or /cancel:",
        parse_mode="Markdown",
    )
    return WAIT_AUTOBAN_THRESHOLD


async def receive_autoban_thresh(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val_txt = update.message.text.strip()
    if not val_txt.isdigit() or int(val_txt) < 1:
        await update.message.reply_text("❌ Please enter a positive whole number (e.g., 3) or /cancel:")
        return WAIT_AUTOBAN_THRESHOLD
    val = int(val_txt)
    await run_db(set_setting, "autoban_abuse_threshold", str(val))
    await update.message.reply_text(f"✅ Abuse max changes updated to `{val}`!", parse_mode="Markdown")
    text_msg, kbd = build_autoban_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="users")
async def admin_autoban_window_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    curr = get_abuse_ban_window()
    await update.callback_query.message.reply_text(
        f"⏱️ **ABUSE WINDOW (SECONDS)**\n\nCurrent window: `{curr}s`\nSend new window duration in seconds (e.g., `25`), or /cancel:",
        parse_mode="Markdown",
    )
    return WAIT_AUTOBAN_WINDOW


async def receive_autoban_window(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val_txt = update.message.text.strip()
    if not val_txt.isdigit() or int(val_txt) < 1:
        await update.message.reply_text("❌ Please enter a positive number of seconds (e.g., 25) or /cancel:")
        return WAIT_AUTOBAN_WINDOW
    val = int(val_txt)
    await run_db(set_setting, "autoban_abuse_window", str(val))
    await update.message.reply_text(f"✅ Abuse window updated to `{val}s`!", parse_mode="Markdown")
    text_msg, kbd = build_autoban_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="users")
async def admin_autoban_days_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    curr = get_inactive_autoban_days()
    await update.callback_query.message.reply_text(
        f"⏳ **INACTIVE AUTO-BAN DAYS**\n\nCurrent threshold: `{curr}` days\nSend minimum inactive days before auto-ban (e.g., `7`), or /cancel:",
        parse_mode="Markdown",
    )
    return WAIT_AUTOBAN_INACTIVE_DAYS


async def receive_autoban_days(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val_txt = update.message.text.strip()
    if not val_txt.isdigit() or int(val_txt) < 1:
        await update.message.reply_text("❌ Please enter a positive number of days (e.g., 7) or /cancel:")
        return WAIT_AUTOBAN_INACTIVE_DAYS
    val = int(val_txt)
    await run_db(set_setting, "autoban_inactive_days", str(val))
    await update.message.reply_text(f"✅ Inactive days threshold updated to `{val}d`!", parse_mode="Markdown")
    text_msg, kbd = build_autoban_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="users")
async def admin_autoban_otps_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    curr = get_inactive_autoban_min_otps()
    await update.callback_query.message.reply_text(
        f"📨 **INACTIVE AUTO-BAN MIN WEEKLY OTPs**\n\nCurrent threshold: `{curr}` OTPs\nSend minimum weekly OTPs required to avoid ban (e.g., `10`), or /cancel:",
        parse_mode="Markdown",
    )
    return WAIT_AUTOBAN_INACTIVE_OTPS


async def receive_autoban_otps(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val_txt = update.message.text.strip()
    if not val_txt.isdigit() or int(val_txt) < 1:
        await update.message.reply_text("❌ Please enter a positive number (e.g., 10) or /cancel:")
        return WAIT_AUTOBAN_INACTIVE_OTPS
    val = int(val_txt)
    await run_db(set_setting, "autoban_inactive_min_otps", str(val))
    await update.message.reply_text(f"✅ Min weekly OTPs threshold updated to `{val}`!", parse_mode="Markdown")
    text_msg, kbd = build_autoban_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="extra")
async def set_rank1_bonus_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text("Enter bonus amount for **Top 1** user (e.g., 50):", parse_mode="Markdown")
    return WAIT_RANK1_BONUS


async def receive_rank1_bonus(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = float(update.message.text.strip())
        if val < 0: val = 0.0
    except ValueError:
        val = 50.0
    await run_db(set_setting, "rank_bonus_1", str(val))
    await update.message.reply_text(f"✅ Top 1 bonus set to `{fmt_num(val)} ৳`!", parse_mode="Markdown")
    text_msg, kbd = build_ranking_bonus_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="extra")
async def set_rank2_bonus_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text("Enter bonus amount for **Top 2** user (e.g., 30):", parse_mode="Markdown")
    return WAIT_RANK2_BONUS


async def receive_rank2_bonus(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = float(update.message.text.strip())
        if val < 0: val = 0.0
    except ValueError:
        val = 30.0
    await run_db(set_setting, "rank_bonus_2", str(val))
    await update.message.reply_text(f"✅ Top 2 bonus set to `{fmt_num(val)} ৳`!", parse_mode="Markdown")
    text_msg, kbd = build_ranking_bonus_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="extra")
async def set_rank3_bonus_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text("Enter bonus amount for **Top 3** user (e.g., 20):", parse_mode="Markdown")
    return WAIT_RANK3_BONUS


async def receive_rank3_bonus(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = float(update.message.text.strip())
        if val < 0: val = 0.0
    except ValueError:
        val = 20.0
    await run_db(set_setting, "rank_bonus_3", str(val))
    await update.message.reply_text(f"✅ Top 3 bonus set to `{fmt_num(val)} ৳`!", parse_mode="Markdown")
    text_msg, kbd = build_ranking_bonus_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="links")
async def set_dev_name_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the new Developer Name/Tag (e.g., John Doe):")
    return WAIT_DEV_NAME


async def receive_dev_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    new_name = update.message.text.strip()
    await run_db(set_setting, "dev_username", new_name)
    await update.message.reply_text(f"✅ Developer Name updated!\nCurrent Name: `{escape_md(new_name)}`", parse_mode="Markdown")
    text_msg, kbd = build_edit_links_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="links")
async def set_dev_link_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the new Developer Telegram Link/Username (e.g., https://t.me/developer or @developer):")
    return WAIT_DEV_LINK


async def receive_dev_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    new_link = update.message.text.strip()
    await run_db(set_setting, "dev_link", new_link)
    await update.message.reply_text(f"✅ Developer Link updated!\nCurrent Link: {escape_md(new_link)}", parse_mode="Markdown")
    text_msg, kbd = build_edit_links_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="withdraw_settings")
async def admin_add_w_method_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text("Enter new payment method name (e.g., PayTM, Rocket):")
    return WAIT_NEW_WITHDRAW_METHOD


async def receive_new_withdraw_method(update: Update, context: ContextTypes.DEFAULT_TYPE):
    method_name = update.message.text.strip()
    if method_name:
        await run_db(add_withdraw_method_sync, method_name)
        await update.message.reply_text(f"✅ Payment method **{escape_md(method_name)}** added!", parse_mode="Markdown")
    text_msg, kbd = build_withdraw_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="withdraw_settings")
async def admin_set_min_w_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text("Enter new minimum withdraw amount (e.g., 50):")
    return WAIT_MIN_WITHDRAW_AMOUNT


async def receive_min_withdraw_amount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = float(update.message.text.strip())
        if val < 0:
            val = 0.0
    except ValueError:
        val = 50.0
    await run_db(set_setting, "min_withdraw_amount", str(val))
    await update.message.reply_text(f"✅ Minimum withdraw amount set to `{fmt_num(val)} ৳`!", parse_mode="Markdown")
    text_msg, kbd = build_withdraw_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="payouts")
async def admin_reject_w_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    req_id = int(query.data.split(":", 2)[2])
    context.user_data['reject_req_id'] = req_id
    await query.message.reply_text(f"Please enter the rejection reason for Withdraw Request `#{req_id}`:", parse_mode="Markdown")
    return WAIT_REJECT_REASON


async def receive_reject_reason(update: Update, context: ContextTypes.DEFAULT_TYPE):
    reason_text = update.message.text.strip()
    req_id = context.user_data.get('reject_req_id')

    if req_id:
        req = await run_db(get_withdraw_request_by_id_sync, req_id)
        if req and req["status"] == "pending":
            ok = await run_db(atomic_transition_withdraw_status_sync, req_id, "pending", "rejected", reason_text)
            if ok:
                await run_db(refund_user_balance_sync, req["user_id"], req["amount"])
                user_msg = (
                    "❌ <b>WITHDRAWAL REJECTED</b>\n\n"
                    f"Your withdrawal request of <b>{fmt_num(req['amount'])} ৳</b> via <b>{html.escape(req['method'])}</b> has been rejected.\n"
                    f"<b>{fmt_num(req['amount'])} ৳</b> has been refunded to your wallet.\n\n"
                    "<b>Reason:</b>\n"
                    f"<blockquote expandable>{html.escape(reason_text)}</blockquote>"
                )
                try:
                    await context.bot.send_message(chat_id=req["user_id"], text=user_msg, parse_mode="HTML")
                except Exception as e:
                    logging.error(f"Failed to send rejection notification: {e}")
                await update.message.reply_text(f"✅ Request `#{req_id}` rejected and user notified.", parse_mode="Markdown")
            else:
                await update.message.reply_text("❌ Could not reject — request was already processed.")
        else:
            await update.message.reply_text("❌ Request was already processed or not found.")

    context.user_data.pop('reject_req_id', None)
    text_msg, kbd = await run_db(build_admin_withdraw_requests_view, 1)
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="services")
async def admin_add_service_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text("Enter the service name (e.g., TikTok, Facebook):")
    return ADD_SERVICE


@admin_only(perm="services")
async def admin_add_service_with_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    service = _resolve_srv_token(query.data.split(":", 3)[3])
    context.user_data['service_name'] = service
    await query.message.reply_text(
        f"Service <b>{safe_html_escape(service)}</b> selected.\n\nEnter country name (e.g., Bangladesh, Nepal):",
        parse_mode="HTML"
    )
    return ADD_COUNTRY


@admin_only(perm="services")
async def admin_edit_service_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    service = _resolve_srv_token(query.data.split(":", 3)[3])
    context.user_data['edit_old_service'] = service
    await query.message.reply_text(
        f"✏️ <b>EDIT SERVICE NAME</b>\n\n"
        f"Current name: <b>{safe_html_escape(service)}</b>\n\n"
        f"Send the new service name (supports premium emojis), or type /cancel to abort:",
        parse_mode="HTML",
    )
    return WAIT_EDIT_SERVICE_NAME


async def receive_edit_service_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    new_service = entities_to_tg_emoji(raw, ents).strip()
    old_service = context.user_data.get('edit_old_service')

    if not old_service or not new_service:
        await update.message.reply_text("❌ Service name cannot be empty. Please try again or type /cancel:")
        return WAIT_EDIT_SERVICE_NAME

    ok, err = await run_db(rename_service_db, old_service, new_service)
    if not ok:
        await update.message.reply_text(f"❌ {html.escape(err)}\nPlease enter another name or type /cancel:", parse_mode="HTML")
        return WAIT_EDIT_SERVICE_NAME

    context.user_data.pop('edit_old_service', None)
    await update.message.reply_text(
        f"✅ Service renamed to <b>{safe_html_escape(new_service)}</b>!",
        parse_mode="HTML",
    )
    text_msg, kbd = build_service_manage_view(new_service)
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="HTML")
    return ConversationHandler.END


@admin_only(perm="services")
async def admin_country_add_numbers_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    service, country = _resolve_sc_token(query.data.split(":", 3)[3])
    context.user_data['service_name'] = service
    context.user_data['country_name'] = country
    context.user_data['payout_amount'] = get_payout_sync(service, country)
    context.user_data['add_numbers_return_country'] = True
    await query.message.reply_text(
        f"➕ <b>ADD NUMBERS</b>\n\n"
        f"🏷️ Service: <b>{safe_html_escape(service)}</b>\n"
        f"🏳️ Country: <b>{safe_html_escape(country)}</b>\n\n"
        f"Send the numbers (as a text file or one number per line):",
        parse_mode="HTML",
    )
    return ADD_NUMBERS


@admin_only(perm="services")
async def admin_edit_country_name_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    service, country = _resolve_sc_token(query.data.split(":", 3)[3])
    context.user_data['edit_srv'] = service
    context.user_data['edit_old_country'] = country
    await query.message.reply_text(
        f"✏️ <b>EDIT COUNTRY NAME</b>\n\n"
        f"🏷️ Service: <b>{safe_html_escape(service)}</b>\n"
        f"🌍 Current Country Name: <b>{safe_html_escape(country)}</b>\n\n"
        f"Send the new <b>Country Name</b> (supports emojis), or send <code>skip</code> to keep current name:",
        parse_mode="HTML",
    )
    return WAIT_EDIT_COUNTRY_NAME


async def receive_edit_country_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    val = entities_to_tg_emoji(raw, ents).strip()
    service = context.user_data.get('edit_srv', '')
    old_country = context.user_data.get('edit_old_country', '')

    if not service or not old_country:
        return ConversationHandler.END

    if val.lower() == "skip" or not val:
        new_country = old_country
    else:
        if val != old_country and val in SERVICES_CACHE.get(service, {}):
            await update.message.reply_text(
                f"❌ Country <b>{safe_html_escape(val)}</b> already exists in this service.\n"
                f"Enter another name, send <code>skip</code>, or type /cancel:",
                parse_mode="HTML",
            )
            return WAIT_EDIT_COUNTRY_NAME
        new_country = val

    context.user_data['edit_new_country'] = new_country
    curr_short = get_country_short_sync(service, old_country)
    await update.message.reply_text(
        f"🔤 Current Short Name: {safe_html_escape(curr_short)}\n\n"
        f"Enter the new <b>Short Name</b> (e.g., <code>BD</code>, <code>US</code>, <code>LK</code>), "
        f"or send <code>skip</code> to keep current:",
        parse_mode="HTML",
    )
    return WAIT_EDIT_COUNTRY_SHORT


async def receive_edit_country_short(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    val = entities_to_tg_emoji(raw, ents).strip()

    service = context.user_data.get('edit_srv', '')
    old_country = context.user_data.get('edit_old_country', '')
    new_country = context.user_data.get('edit_new_country', old_country)

    if not service or not old_country:
        return ConversationHandler.END

    final_country = old_country
    if new_country != old_country:
        ok, err = await run_db(rename_country_db, service, old_country, new_country)
        if not ok:
            await update.message.reply_text(f"❌ {html.escape(err)}", parse_mode="HTML")
            for k in ('edit_srv', 'edit_old_country', 'edit_new_country'):
                context.user_data.pop(k, None)
            return ConversationHandler.END
        final_country = new_country

    if val.lower() != "skip" and val:
        await run_db(set_country_short_sync, service, final_country, val)

    for k in ('edit_srv', 'edit_old_country', 'edit_new_country'):
        context.user_data.pop(k, None)

    await update.message.reply_text(
        f"✅ Updated country <b>{safe_html_escape(final_country)}</b>!",
        parse_mode="HTML",
    )
    text_msg, kbd = build_country_edit_view(service, final_country)
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="HTML")
    return ConversationHandler.END


@admin_only(perm="services")
async def admin_country_edit_payout_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    service, country = _resolve_sc_token(query.data.split(":", 3)[3])
    context.user_data['pay_edit_service'] = service
    context.user_data['pay_edit_country'] = country
    context.user_data['pay_flow'] = 'country_edit'

    curr = get_payout_sync(service, country)
    await query.message.reply_text(
        f"💰 Editing payout for:\n"
        f"🏷️ Service: <b>{safe_html_escape(service)}</b>\n"
        f"🏳️ Country: <b>{safe_html_escape(country)}</b>\n\n"
        f"Current payout: <code>{fmt_num(curr)} ৳</code>\n"
        f"Send new amount (or send <code>default</code> for {fmt_num(DEFAULT_PAYOUT)} ৳):",
        parse_mode="HTML",
    )
    return WAIT_PAYOUT_AMOUNT


async def receive_service_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    context.user_data['service_name'] = entities_to_tg_emoji(raw, ents).strip()
    await update.message.reply_text("Enter country name (e.g., Bangladesh, Nepal):")
    return ADD_COUNTRY


async def receive_country_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    country = entities_to_tg_emoji(raw, ents).strip()
    context.user_data['country_name'] = country
    service = context.user_data.get('service_name', '')

    existing_short = get_country_short_sync(service, country) if service else country
    has_custom_short = (existing_short != country)

    if has_custom_short:
        await update.message.reply_text(
            f"🏳️ Country: <b>{safe_html_escape(country)}</b>\n"
            f"🔤 Current short form: {safe_html_escape(existing_short)}\n\n"
            f"Enter a new <b>short form</b> (e.g., <code>BD</code>, <code>US</code>, <code>IND</code>), "
            "or send <code>skip</code> to keep the current one:",
            parse_mode="HTML"
        )
    else:
        await update.message.reply_text(
            f"🏳️ Country: <b>{safe_html_escape(country)}</b>\n\n"
            f"Enter a <b>short form</b> for this country (e.g., <code>BD</code>, <code>US</code>, <code>IND</code>).\n"
            f"This will be shown in OTP group messages:",
            parse_mode="HTML"
        )
    return WAIT_COUNTRY_SHORT


async def receive_country_short(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text or ""
    ents = update.message.entities or []
    val = entities_to_tg_emoji(raw, ents).strip()
    
    country = context.user_data.get('country_name', '')
    service = context.user_data.get('service_name', '')

    if val.lower() == 'skip':
        short = get_country_short_sync(service, country) if service else country
    else:
        short = val
        await run_db(set_country_short_sync, service, country, short)

    existing_payout = get_payout_sync(service, country) if service else DEFAULT_PAYOUT
    hint = ""
    if service and country in PAYOUTS_CACHE.get(service, {}):
        hint = f"\n⚠️ This country already exists with payout <code>{fmt_num(existing_payout)} ৳</code>. Sending a new payout will overwrite it."

    await update.message.reply_text(
        f"✅ Short form set to {safe_html_escape(short)}.\n\n"
        f"💵 Enter the <b>payout amount (৳)</b> each user will receive per OTP "
        f"for <b>{safe_html_escape(service)}</b> → <b>{safe_html_escape(country)}</b>.\n\n"
        f"Default: <code>{fmt_num(DEFAULT_PAYOUT)} ৳</code> (send <code>default</code> to use this)."
        f"{hint}",
        parse_mode="HTML"
    )
    return WAIT_PAYOUT_AMOUNT


async def receive_numbers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    numbers = []
    if update.message.document:
        file = await context.bot.get_file(update.message.document.file_id)
        content = (await file.download_as_bytearray()).decode('utf-8')
        numbers = [line.strip() for line in content.splitlines() if line.strip()]
    elif update.message.text:
        numbers = [line.strip() for line in update.message.text.splitlines() if line.strip()]

    service = context.user_data.get('service_name')
    country = context.user_data.get('country_name')
    payout = context.user_data.get('payout_amount', DEFAULT_PAYOUT)
    return_country = bool(context.user_data.get('add_numbers_return_country'))

    if service and country and numbers:
        valid_count = await run_db(save_numbers_sync, service, country, numbers, payout)
        short = get_country_short_sync(service, country)
        uid_curr = update.effective_user.id if update.effective_user else 0
        await update.message.reply_text(
            f"✅ Successfully added <b>{valid_count}</b> numbers!\n"
            f"🏳️ Country: <b>{safe_html_escape(country)}</b> ({safe_html_escape(short)})\n"
            f"💰 Payout per OTP: <code>{fmt_num(payout)} ৳</code>",
            reply_markup=get_admin_keyboard(user_id=uid_curr), parse_mode="HTML"
        )
        if return_country:
            text_msg, kbd = build_country_manage_view(service, country)
            await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="HTML")
    else:
        uid_curr = update.effective_user.id if update.effective_user else 0
        await update.message.reply_text("Incomplete data provided. Please try again.", reply_markup=get_admin_keyboard(user_id=uid_curr))

    for key in ('service_name', 'country_name', 'payout_amount', 'cc_length', 'country_short', 'add_numbers_return_country'):
        context.user_data.pop(key, None)
    context.user_data['current_menu'] = 'admin'
    return ConversationHandler.END


@admin_only(perm="admins")
async def admin_add_admin_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the Telegram User ID of the new Admin (e.g., 123456789):")
    else:
        await update.message.reply_text("Enter the Telegram User ID of the new Admin (e.g., 123456789):")
    return WAIT_ADMIN_ID


async def receive_admin_id(update: Update, context: ContextTypes.DEFAULT_TYPE):
    input_text = update.message.text.strip()
    if not input_text.isdigit():
        await update.message.reply_text("❌ Invalid Telegram User ID! Please enter numbers only.\nType /cancel to abort.")
        return WAIT_ADMIN_ID
    context.user_data['new_admin_id'] = int(input_text)
    await update.message.reply_text("Enter Admin Name/Tag (e.g., Co-Admin John):")
    return WAIT_ADMIN_NAME


async def receive_admin_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    admin_name = update.message.text.strip()
    new_id = context.user_data.get('new_admin_id')

    if new_id and admin_name:
        await run_db(add_admin_sync, new_id, admin_name)
        if new_id != ADMIN_ID:
            await run_db(set_admin_perms_sync, new_id, "custom", {k: False for k, _ in ADMIN_PERMISSIONS})
        context.user_data.pop('new_admin_id', None)
        text_msg, kbd = build_admin_role_picker_view(new_id, admin_name)
        await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
        return ConversationHandler.END

    await update.message.reply_text("❌ Failed to add admin. Incomplete data.")
    context.user_data.pop('new_admin_id', None)
    text_msg, kbd = build_admin_control_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="api")
async def admin_add_panel_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['panel_flow'] = 'standard'
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the Panel Name (e.g., Main Provider, Panel 1):")
    else:
        await update.message.reply_text("Enter the Panel Name (e.g., Main Provider, Panel 1):")
    return WAIT_PANEL_NAME


@admin_only(perm="api")
async def admin_add_custom_panel_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['panel_flow'] = 'custom'
    await update.callback_query.message.reply_text(
        "🔧 **CUSTOM API SETUP**\n\n"
        "You will provide the full URL and JSON path mappings step by step.\n\n"
        "First, enter the Panel Name (e.g., Custom Provider 1):",
        parse_mode="Markdown"
    )
    return WAIT_PANEL_NAME


@admin_only(perm="api")
async def admin_add_captcha_panel_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['panel_flow'] = 'captcha'
    await update.callback_query.message.reply_text(
        "🔐 **CAPTCHA PANEL SETUP**\n\n"
        "This panel uses form-login with arithmetic captcha (e.g., `5 + 3 = ?`).\n\n"
        "**Step 1/8:** Enter the Panel Name (e.g., `Main Captcha Panel`):",
        parse_mode="Markdown"
    )
    return WAIT_PANEL_NAME


@admin_only(perm="api")
async def admin_add_augestel_panel_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['panel_flow'] = 'augestel'
    await update.callback_query.message.reply_text(
        "📡 **AUGESTEL PANEL SETUP**\n\n"
        "This panel logs into augestel.com with email and password.\n\n"
        "**Step 1/4:** Enter the Panel Name (e.g., `Main Augestel Panel`):",
        parse_mode="Markdown"
    )
    return WAIT_PANEL_NAME


async def receive_panel_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['new_api_name'] = update.message.text.strip()
    flow = context.user_data.get('panel_flow')

    if flow == 'custom':
        await update.message.reply_text(
            "Enter the **FULL API URL** (e.g., `https://api.example.com/otps?key=ABC`):",
            parse_mode="Markdown"
        )
        return WAIT_PANEL_URL

    elif flow == 'captcha':
        await update.message.reply_text(
            "**Step 2/8:** Enter the **Login URL** (e.g., `http://example.com/login`):",
            parse_mode="Markdown"
        )
        return WAIT_CPT_LOGIN_URL

    elif flow == 'augestel':
        await update.message.reply_text(
            "**Step 2/4:** Enter the **Panel Email**:",
            parse_mode="Markdown"
        )
        return WAIT_AUG_EMAIL

    else:
        await update.message.reply_text("Enter Base API URL (e.g., http://domain.com/viewstasx):")
        return WAIT_PANEL_URL


async def receive_panel_url(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['new_api_url'] = update.message.text.strip()
    await update.message.reply_text(
        "Enter API Key / Token (or type `skip` if not needed):"
    )
    return WAIT_PANEL_TOKEN


async def receive_panel_token(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tok = update.message.text.strip()
    if tok.lower() == "skip":
        tok = ""
    context.user_data['new_api_token'] = tok
    await update.message.reply_text("Enter Polling Interval in seconds (Default: 5, Min: 3.1, Max: 120):")
    return WAIT_PANEL_INTERVAL


async def receive_panel_interval(update: Update, context: ContextTypes.DEFAULT_TYPE):
    input_text = update.message.text.strip()
    try:
        interval_val = float(input_text)
        if interval_val < 3.1:
            interval_val = 3.1
        elif interval_val > 120.0:
            interval_val = 120.0
    except ValueError:
        interval_val = 5.0

    context.user_data['new_api_interval'] = interval_val

    if context.user_data.get('panel_flow') == 'augestel':
        return await _save_augestel_panel(update, context)

    if context.user_data.get('panel_flow') == 'custom':
        await update.message.reply_text(
            "🧩 **JSON MAPPING — STEP 1/7**\n\n"
            "Enter the JSON path for the **status field** (e.g., `status`, `success`, `code`).\n"
            "Or type `skip` to skip status check.",
            parse_mode="Markdown"
        )
        return WAIT_MAP_STATUS_PATH

    p_name = context.user_data.get('new_api_name')
    p_url = context.user_data.get('new_api_url')
    p_token = context.user_data.get('new_api_token')

    if p_name and p_url:
        pid = await run_db(save_api_panel_sync, p_name, p_url, p_token or "", interval_val, None)
        await update.message.reply_text(
            f"✅ **Standard API Panel Connected!**\n\n📌 Name: `{escape_md(p_name)}`\n⏱️ Polling: `{interval_val}s`",
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text("❌ Incomplete panel data.")

    for key in ('new_api_name', 'new_api_url', 'new_api_token', 'panel_flow', 'new_api_interval'):
        context.user_data.pop(key, None)
    text_msg, kbd = build_api_panels_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


async def receive_map_status_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if val.lower() == "skip":
        context.user_data['map_status_path'] = None
        await update.message.reply_text(
            "🧩 **STEP 2/7 — skipped status check**\n\n"
            "Enter the JSON path for the **data array** (e.g., `data`, `messages`, `result.items`):",
            parse_mode="Markdown"
        )
        return WAIT_MAP_DATA_PATH
    context.user_data['map_status_path'] = val
    await update.message.reply_text(
        "🧩 **STEP 2/7**\n\n"
        "Enter the **success value** for the status field (e.g., `success`, `true`, `1`, `200`):",
        parse_mode="Markdown"
    )
    return WAIT_MAP_STATUS_VALUE


async def receive_map_status_value(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['map_status_value'] = update.message.text.strip()
    await update.message.reply_text(
        "🧩 **STEP 3/7**\n\n"
        "Enter the JSON path for the **data array** (e.g., `data`, `messages`, `result.items`):",
        parse_mode="Markdown"
    )
    return WAIT_MAP_DATA_PATH


async def receive_map_data_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val:
        val = "data"
    context.user_data['map_data_path'] = val
    await update.message.reply_text(
        "🧩 **STEP 4/7**\n\n"
        "Enter the JSON path for the **phone number** inside each item (e.g., `num`, `phone`, `number`):",
        parse_mode="Markdown"
    )
    return WAIT_MAP_NUM_PATH


async def receive_map_num_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val:
        val = "num"
    context.user_data['map_num_path'] = val
    await update.message.reply_text(
        "🧩 **STEP 5/7**\n\n"
        "Enter the JSON path for the **message / OTP text** inside each item (e.g., `message`, `sms`, `text`):",
        parse_mode="Markdown"
    )
    return WAIT_MAP_MSG_PATH


async def receive_map_msg_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val:
        val = "message"
    context.user_data['map_msg_path'] = val
    await update.message.reply_text(
        "🧩 **STEP 6/7**\n\n"
        "Enter the JSON path for the **datetime** inside each item (e.g., `dt`, `time`, `created_at`).\n"
        "This is used for deduplication — different timestamps mean different messages.",
        parse_mode="Markdown"
    )
    return WAIT_MAP_DT_PATH


async def receive_map_dt_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val:
        val = "dt"
    context.user_data['map_dt_path'] = val
    await update.message.reply_text(
        "🧩 **STEP 7/7**\n\n"
        "Enter the JSON path for the **payout** value (e.g., `payout`, `amount`).\n"
        "Or type `skip` — payout will come from your configured service payouts.",
        parse_mode="Markdown"
    )
    return WAIT_MAP_PAYOUT_PATH


async def receive_map_payout_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if val.lower() == "skip" or not val:
        context.user_data['map_payout_path'] = None
    else:
        context.user_data['map_payout_path'] = val
    await update.message.reply_text(
        "🧩 **OPTIONAL — STEP 8/8**\n\n"
        "Enter the JSON path for the **service/client name** inside each item (e.g., `cli`, `service`).\n"
        "Or type `skip` — service name will come from your allocation lookup.",
        parse_mode="Markdown"
    )
    return WAIT_MAP_CLI_PATH


async def receive_map_cli_path(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if val.lower() == "skip" or not val:
        context.user_data['map_cli_path'] = None
    else:
        context.user_data['map_cli_path'] = val

    mapping = {
        "status_path": context.user_data.get('map_status_path'),
        "status_value": context.user_data.get('map_status_value', 'success'),
        "data_path": context.user_data.get('map_data_path', 'data'),
        "num_path": context.user_data.get('map_num_path', 'num'),
        "msg_path": context.user_data.get('map_msg_path', 'message'),
        "dt_path": context.user_data.get('map_dt_path', 'dt'),
        "payout_path": context.user_data.get('map_payout_path'),
        "cli_path": context.user_data.get('map_cli_path'),
    }
    mapping_json = json.dumps(mapping)

    p_name = context.user_data.get('new_api_name')
    p_url = context.user_data.get('new_api_url')
    p_token = context.user_data.get('new_api_token') or ""
    p_interval = context.user_data.get('new_api_interval', 5.0)

    if p_name and p_url:
        pid = await run_db(save_api_panel_sync, p_name, p_url, p_token, p_interval, mapping_json)
        await update.message.reply_text(
            f"✅ **Custom API Panel Connected!**\n\n"
            f"📌 Name: `{escape_md(p_name)}`\n"
            f"⏱️ Polling: `{p_interval}s`\n"
            f"🧩 Mapping saved.",
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text("❌ Incomplete panel data.")

    for key in ('new_api_name', 'new_api_url', 'new_api_token', 'panel_flow',
                'new_api_interval', 'map_status_path', 'map_status_value',
                'map_data_path', 'map_num_path', 'map_msg_path', 'map_dt_path',
                'map_payout_path', 'map_cli_path'):
        context.user_data.pop(key, None)

    text_msg, kbd = build_api_panels_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


async def receive_cpt_login_url(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['cpt_login_url'] = update.message.text.strip()
    await update.message.reply_text("**Step 3/8:** Enter the **Panel Username**:", parse_mode="Markdown")
    return WAIT_CPT_USERNAME


async def receive_cpt_username(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['cpt_username'] = update.message.text.strip()
    await update.message.reply_text("**Step 4/8:** Enter the **Panel Password**:", parse_mode="Markdown")
    return WAIT_CPT_PASSWORD


async def receive_cpt_password(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['cpt_password'] = update.message.text.strip()
    await update.message.reply_text(
        "**Step 5/8:** Enter the **Message Link** (URL where the CDR/OTP table loads):\n"
        "Example: `http://example.com/client/SMSCDRStats`\n"
        "Or send `skip` to use default.",
        parse_mode="Markdown"
    )
    return WAIT_CPT_MSG_LINK


async def receive_cpt_msg_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if val.lower() == "skip":
        val = ""
    context.user_data['cpt_msg_link'] = val
    await update.message.reply_text(
        "**Step 6/8:** Enter the **Number Column Name** (e.g., `number`, `phone`, `msisdn`):",
        parse_mode="Markdown"
    )
    return WAIT_CPT_NUM_COL_NAME


async def receive_cpt_num_col_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['cpt_num_col_name'] = update.message.text.strip()
    await update.message.reply_text(
        "**Step 7/8:** Enter the **Number Column Index** (1-based, e.g., `3`):",
        parse_mode="Markdown"
    )
    return WAIT_CPT_NUM_COL_IDX


async def receive_cpt_num_col_idx(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return WAIT_CPT_NUM_COL_IDX
    context.user_data['cpt_num_col_idx'] = int(val)
    await update.message.reply_text(
        "**Step 8/8:** Enter the **Message Column Name** (e.g., `message`, `sms`, `text`):",
        parse_mode="Markdown"
    )
    return WAIT_CPT_MSG_COL_NAME


async def receive_cpt_msg_col_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['cpt_msg_col_name'] = update.message.text.strip()
    await update.message.reply_text(
        "**Final Step:** Enter the **Message Column Index** (1-based, e.g., `5`):",
        parse_mode="Markdown"
    )
    return WAIT_CPT_MSG_COL_IDX


async def receive_cpt_msg_col_idx(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return WAIT_CPT_MSG_COL_IDX

    context.user_data['cpt_msg_col_idx'] = int(val)
    await update.message.reply_text(
        "🆕 **Date/Time Column (Optional)**\n\n"
        "This is used to **prevent OTP duplication** — same as API panel `dt_path`.\n\n"
        "Enter the **Date/Time column name** in the panel table (e.g., `date`, `time`, `datetime`, `created_at`).\n\n"
        "Or send `skip` if the table doesn't have a date column.",
        parse_mode="Markdown"
    )
    return WAIT_CPT_DT_COL_NAME


async def receive_cpt_dt_col_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if val.lower() == "skip" or not val:
        context.user_data['cpt_dt_col_name'] = ""
        context.user_data['cpt_dt_col_idx'] = 0
        return await _save_captcha_panel(update, context)

    context.user_data['cpt_dt_col_name'] = val
    await update.message.reply_text(
        "Enter the **Date/Time Column Index** (1-based, e.g., `1` or `6`).\n\n"
        "Type `0` if you don't know the index — the bot will auto-detect by column name.",
        parse_mode="Markdown"
    )
    return WAIT_CPT_DT_COL_IDX


async def receive_cpt_dt_col_idx(update: Update, context: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip()
    if not val.isdigit():
        await update.message.reply_text("❌ Please enter a valid number (0 for auto-detect).")
        return WAIT_CPT_DT_COL_IDX
    context.user_data['cpt_dt_col_idx'] = int(val)
    return await _save_captcha_panel(update, context)


async def receive_aug_email(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['aug_email'] = update.message.text.strip()
    await update.message.reply_text("**Step 3/4:** Enter the **Panel Password**:", parse_mode="Markdown")
    return WAIT_AUG_PASSWORD


async def receive_aug_password(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['aug_password'] = update.message.text.strip()
    await update.message.reply_text(
        "**Step 4/5:** Enter the **API Key** (Get it from Augestel -> SMS API -> API Credentials).\n"
        "Example: `sk_live_...`", 
        parse_mode="Markdown"
    )
    return WAIT_AUG_API_KEY

async def receive_aug_api_key(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['aug_api_key'] = update.message.text.strip()
    await update.message.reply_text("**Step 5/5:** Enter Polling Interval for API in seconds (Default: 13, Min: 13, Max: 120):", parse_mode="Markdown")
    return WAIT_PANEL_INTERVAL

async def _save_augestel_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cfg = {
        "_panel_type": "augestel",
        "login_url": AUGESTEL_LOGIN_URL,
        "dashboard_url": AUGESTEL_DASHBOARD_URL,
        "email": context.user_data.get('aug_email', ''),
        "password": context.user_data.get('aug_password', ''),
        "api_key": context.user_data.get('aug_api_key', ''), # নতুন API Key
    }
    p_name = context.user_data.get('new_api_name', '')
    p_interval = context.user_data.get('new_api_interval', 13.0) or 13.0
    
    if p_name and cfg["email"] and cfg["password"] and cfg["api_key"]:
        pid = await run_db(
            save_api_panel_sync,
            p_name, AUGESTEL_LOGIN_URL, "", p_interval, json.dumps(cfg),
        )
        await update.message.reply_text(
            f"✅ **Augestel Panel Added!**\n\n"
            f"📌 Name: `{escape_md(p_name)}`\n"
            f"👤 Email: `{escape_md(cfg['email'])}`\n"
            f"🔑 API Key: `{mask_api_key(cfg['api_key'])}`\n"
            f"⏱️ API Polling: `{p_interval}s`\n\n"
            f"WebSocket will start automatically. API will act as backup.",
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text("❌ Incomplete panel data.")
    
    for k in ('new_api_name', 'new_api_interval', 'panel_flow', 'aug_email', 'aug_password', 'aug_api_key'):
        context.user_data.pop(k, None)
    
    text_msg, kbd = build_api_panels_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


async def _save_captcha_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cfg = {
        "_panel_type": "captcha",
        "login_url": context.user_data.get('cpt_login_url', ''),
        "username": context.user_data.get('cpt_username', ''),
        "password": context.user_data.get('cpt_password', ''),
        "msg_link": context.user_data.get('cpt_msg_link', ''),
        "num_col_name": context.user_data.get('cpt_num_col_name', 'number'),
        "num_col_idx": context.user_data.get('cpt_num_col_idx', 1),
        "msg_col_name": context.user_data.get('cpt_msg_col_name', 'message'),
        "msg_col_idx": context.user_data.get('cpt_msg_col_idx', 1),
        "dt_col_name": context.user_data.get('cpt_dt_col_name', ''),
        "dt_col_idx": context.user_data.get('cpt_dt_col_idx', 0),
    }

    p_name = context.user_data.get('new_api_name', '')
    p_interval = context.user_data.get('new_api_interval', 5.0) or 5.0

    if p_name and cfg["login_url"]:
        pid = await run_db(
            save_api_panel_sync,
            p_name, cfg["login_url"], "", p_interval, json.dumps(cfg),
        )
        dt_info = ""
        if cfg["dt_col_name"]:
            dt_info = f"\n📅 Date Column: `{escape_md(cfg['dt_col_name'])}` (idx `{cfg['dt_col_idx']}`)"
        await update.message.reply_text(
            f"✅ **Captcha Panel Added!**\n\n"
            f"📌 Name: `{escape_md(p_name)}`\n"
            f"🌐 Login URL: `{escape_md(cfg['login_url'])}`\n"
            f"👤 User: `{escape_md(cfg['username'])}`\n"
            f"⏱️ Polling: `{p_interval}s`{dt_info}\n\n"
            f"Bot will auto-login and start fetching shortly.",
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text("❌ Incomplete panel data.")

    for k in ('new_api_name', 'new_api_interval', 'panel_flow',
              'cpt_login_url', 'cpt_username', 'cpt_password', 'cpt_msg_link',
              'cpt_num_col_name', 'cpt_num_col_idx', 'cpt_msg_col_name',
              'cpt_msg_col_idx', 'cpt_dt_col_name', 'cpt_dt_col_idx'):
        context.user_data.pop(k, None)

    text_msg, kbd = build_api_panels_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="extra")
async def admin_fj_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.message.reply_text(
        "➕ **ADD CHANNEL/GROUP FOR FORCE JOIN**\n\n"
        "**Step 1/4:** Send the Chat ID or @username.\n\n"
        "Examples:\n"
        "• `-1001234567890` (recommended — works with private too)\n"
        "• `@mychannel`\n\n"
        "⚠️ Bot must be an admin in this chat.\n"
        "Type /cancel to abort.",
        parse_mode="Markdown"
    )
    return WAIT_FJ_CHAT_ID


async def receive_fj_chat_id(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text.strip()
    cid, username = _normalize_chat_id(raw)
    if cid is None and not username:
        await update.message.reply_text("❌ Invalid chat ID / username. Try again or /cancel.")
        return WAIT_FJ_CHAT_ID
    context.user_data['fj_chat_id'] = cid if cid is not None else username
    await update.message.reply_text(
        "**Step 2/4:** Send a display title (e.g., `Our Official Channel`):",
        parse_mode="Markdown"
    )
    return WAIT_FJ_CHAT_TITLE


async def receive_fj_chat_title(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['fj_chat_title'] = update.message.text.strip() or "Channel"
    await update.message.reply_text(
        "**Step 3/4:** Send the invite link (e.g., `https://t.me/yourchannel`):",
        parse_mode="Markdown"
    )
    return WAIT_FJ_CHAT_LINK


async def receive_fj_chat_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    link = update.message.text.strip()
    if not (link.startswith("http://") or link.startswith("https://") or link.startswith("t.me/")):
        await update.message.reply_text("❌ Invalid link. Must start with http:// or https://")
        return WAIT_FJ_CHAT_LINK
    if link.startswith("t.me/"):
        link = "https://" + link
    context.user_data['fj_chat_link'] = link
    kbd = InlineKeyboardMarkup([
        [create_button("📢 Channel", callback_data="adm:fj_type:channel", style="primary"),
         create_button("👥 Group", callback_data="adm:fj_type:group", style="primary")]
    ])
    await update.message.reply_text("**Step 4/4:** Select the type:", reply_markup=kbd, parse_mode="Markdown")
    return WAIT_FJ_CHAT_TYPE


async def handle_fj_chat_type(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    ctype = query.data.split(":", 2)[2]

    chat_id = context.user_data.get('fj_chat_id')
    title = context.user_data.get('fj_chat_title', 'Channel')
    link = context.user_data.get('fj_chat_link')

    if not chat_id:
        await query.edit_message_text("❌ Setup failed. Try /cancel and add again.")
        return ConversationHandler.END

    chats = await run_db(get_force_join_chats)
    chats.append({
        "chat_id": chat_id,
        "title": title,
        "link": link,
        "type": ctype,
    })
    await run_db(set_force_join_chats, chats)

    for k in ('fj_chat_id', 'fj_chat_title', 'fj_chat_link'):
        context.user_data.pop(k, None)

    await query.edit_message_text(
        f"✅ Added!\n\n**{escape_md(title)}** ({ctype})\nID: `{chat_id}`",
        parse_mode="Markdown"
    )
    text_msg, kbd = build_force_join_view()
    await query.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="extra")
async def admin_set_refer_pct_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.answer()
    await update.callback_query.message.reply_text(
        "Enter refer commission percentage (e.g., 5 for 5%):\n"
        "Send a number between 0 and 100.\n"
        "Type /cancel to abort."
    )
    return WAIT_REFER_PERCENT


async def receive_refer_pct(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = float(update.message.text.strip())
        if val < 0: val = 0.0
        if val > 100: val = 100.0
    except ValueError:
        await update.message.reply_text("❌ Invalid number. Please send a valid percentage (0-100).")
        return WAIT_REFER_PERCENT
    await run_db(set_setting, "refer_commission_percent", str(val))
    await update.message.reply_text(f"✅ Refer commission set to `{fmt_num(val)}%`!", parse_mode="Markdown")
    text_msg, kbd = build_refer_settings_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="links")
async def set_channel_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the new channel link (e.g., https://t.me/your_channel or @your_channel):")
    return WAIT_CHANNEL


async def receive_channel_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    new_link = update.message.text.strip()
    if not (new_link.startswith("http://") or new_link.startswith("https://") or new_link.startswith("t.me/") or new_link.startswith("@'") or new_link.startswith("@")):  # noqa
        await update.message.reply_text("❌ Invalid link! Please enter a valid URL or Telegram username.\nType /cancel to abort.")
        return WAIT_CHANNEL
    await run_db(set_setting, "channel", new_link)
    await update.message.reply_text(f"✅ Channel link updated!\nCurrent link: {escape_md(new_link)}", parse_mode="Markdown")
    text_msg, kbd = build_edit_links_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="links")
async def set_support_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the new support username/link (e.g., @your_support or https://t.me/your_support):")
    return WAIT_SUPPORT


async def receive_support_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    new_link = update.message.text.strip()
    if not (new_link.startswith("http://") or new_link.startswith("https://") or new_link.startswith("t.me/") or new_link.startswith("@'") or new_link.startswith("@")):  # noqa
        await update.message.reply_text("❌ Invalid username/link!\nType /cancel to abort.")
        return WAIT_SUPPORT
    await run_db(set_setting, "support", new_link)
    await update.message.reply_text(f"✅ Support updated!\nCurrent: {escape_md(new_link)}", parse_mode="Markdown")
    text_msg, kbd = build_edit_links_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="links")
async def set_otplink_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the new OTP Group link (e.g., https://t.me/your_otp_group):")
    return WAIT_OTP_LINK


async def receive_otp_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    new_link = update.message.text.strip()
    if not (new_link.startswith("http://") or new_link.startswith("https://") or new_link.startswith("t.me/")):
        await update.message.reply_text("❌ Invalid link!\nType /cancel to abort.")
        return WAIT_OTP_LINK
    await run_db(set_setting, "otp_group_link", new_link)
    await update.message.reply_text(f"✅ OTP Group link updated!\nCurrent link: {escape_md(new_link)}", parse_mode="Markdown")
    text_msg, kbd = build_edit_links_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="links")
async def set_otpgroupid_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.callback_query:
        await update.callback_query.message.reply_text("Enter the OTP Forward Group Chat ID (e.g., -1001234567890):")
    return WAIT_OTP_GROUP_ID


async def receive_otp_group_id(update: Update, context: ContextTypes.DEFAULT_TYPE):
    new_id = update.message.text.strip()
    await run_db(set_setting, "otp_group_id", new_id)
    await update.message.reply_text(
        f"✅ OTP Forward Group ID updated!\nCurrent: `{escape_md(new_id)}`",
        parse_mode="Markdown"
    )
    text_msg, kbd = build_edit_links_view()
    await update.message.reply_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
    return ConversationHandler.END


@admin_only(perm="broadcast")
async def broadcast_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    all_users = await run_db(get_all_users)
    await update.message.reply_text(
        f"📢 **BROADCAST SYSTEM**\n\n"
        f"Target Audience: `{len(all_users)}` users\n\n"
        f"Send or forward the message you want to broadcast.\nType /cancel to abort.",
        parse_mode="Markdown"
    )
    return WAIT_BROADCAST_MSG


async def receive_broadcast_msg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not (await run_db(has_admin_perm_sync, user_id, "broadcast")):
        return ConversationHandler.END

    all_users = await run_db(get_all_users)
    if not all_users:
        await update.message.reply_text("No users found to broadcast.", reply_markup=get_admin_keyboard(user_id=user_id))
        return ConversationHandler.END

    total = len(all_users)
    status_msg = await update.message.reply_text(
        f"⏳ Broadcasting to `{total}` users...", parse_mode="Markdown"
    )

    from_chat_id = update.effective_chat.id
    msg_id = update.message.message_id

    success_count = 0
    failed_count = 0
    counter_lock = asyncio.Lock()

    async def send_one(target_id: int):
        nonlocal success_count, failed_count
        await _wait_for_broadcast_slot()
        ok = await _safe_send_api(
            context.bot, target_id, "copy_message",
            from_chat_id=from_chat_id, message_id=msg_id,
        )
        async with counter_lock:
            if ok:
                success_count += 1
            else:
                failed_count += 1

    task_sem = asyncio.Semaphore(BROADCAST_CONCURRENCY)

    async def limited_send(uid):
        async with task_sem:
            await send_one(uid)

    tasks = [asyncio.create_task(limited_send(uid)) for uid in all_users]
    try:
        await asyncio.gather(*tasks, return_exceptions=True)
    except Exception as e:
        logging.error(f"Broadcast gather error: {e}")

    report = (
        f"📢 **BROADCAST COMPLETED**\n\n"
        f"✅ Sent: `{success_count}`\n"
        f"❌ Failed: `{failed_count}`\n"
        f"📊 Total: `{total}`"
    )
    try:
        await status_msg.edit_text(report, parse_mode="Markdown")
    except Exception:
        await update.message.reply_text(report, parse_mode="Markdown")
    await update.message.reply_text("Select an option from Admin Menu:", reply_markup=get_admin_keyboard(user_id=user_id))
    return ConversationHandler.END


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for key in ('service_name', 'country_name', 'payout_amount', 'new_api_name',
                'new_api_url', 'new_api_token', 'new_admin_id', 'w_method', 'w_wallet',
                'reject_req_id', 'pay_flow', 'pay_edit_service', 'pay_edit_country',
                'panel_flow', 'new_api_interval', 'map_status_path', 'map_status_value',
                'map_data_path', 'map_num_path', 'map_msg_path', 'map_dt_path',
                'map_payout_path', 'map_cli_path',
                'cpt_login_url', 'cpt_username', 'cpt_password', 'cpt_msg_link',
                'cpt_num_col_name', 'cpt_num_col_idx', 'cpt_msg_col_name',
                'cpt_msg_col_idx', 'cpt_dt_col_name', 'cpt_dt_col_idx',
                'fj_chat_id', 'fj_chat_title', 'fj_chat_link', 'cc_length', 'aug_email', 'aug_password',
                'country_short', 'edit_old_service', 'edit_srv', 'edit_old_country',
                'edit_new_country', 'add_numbers_return_country'):
        context.user_data.pop(key, None)

    if update.message and update.message.text:
        await handle_text_menu(update, context)
    return ConversationHandler.END


def _has_adm_callback_perm(user_id: int, data: str) -> bool:
    if user_id == ADMIN_ID:
        return True
    if not is_admin_sync(user_id):
        return False
    if data == "adm:panel_back":
        return True
    if data == "adm:usr:manager":
        return has_admin_perm_sync(user_id, "users") or has_admin_perm_sync(user_id, "admins")
    if data.startswith("adm:usr:"):
        return has_admin_perm_sync(user_id, "users")
    if data.startswith("adm:ctrl:") or data.startswith("adm:add:") or data.startswith("adm:delconf:") or data.startswith("adm:del:"):
        return has_admin_perm_sync(user_id, "admins")
    if data.startswith("adm:srv:") or data.startswith("adm:c:") or data.startswith("adm:cnt:"):
        return has_admin_perm_sync(user_id, "services")
    if data.startswith("adm:pay:") or data.startswith("adm:w_page:") or data.startswith("adm:w_view:") or data.startswith("adm:w_app:") or data.startswith("adm:w_rej_start:"):
        return has_admin_perm_sync(user_id, "payouts")
    if data.startswith("adm:live:"):
        return has_admin_perm_sync(user_id, "live_receivers")
    if data.startswith("adm:set:"):
        return has_admin_perm_sync(user_id, "links")
    if data.startswith("adm:api:"):
        return has_admin_perm_sync(user_id, "api")
    if data.startswith("adm:setqty:"):
        return has_admin_perm_sync(user_id, "number_qty")
    if data in ("adm:w_settings", "adm:w_add_m", "adm:w_set_min", "adm:w_del_m_list", "adm:toggle:withdraw") or data.startswith("adm:w_del_m:"):
        return has_admin_perm_sync(user_id, "withdraw_settings")
    if data == "adm:extra_back":
        return has_admin_perm_sync(user_id, "extra") or has_admin_perm_sync(user_id, "withdraw_settings")
    if data.startswith("adm:toggle:") or data.startswith("adm:r_") or data.startswith("adm:refer_") or data.startswith("adm:fj_") or data.startswith("adm:cliemoji:"):
        return has_admin_perm_sync(user_id, "extra")
    return True


async def handle_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data
    user_id = query.from_user.id
    first_name = query.from_user.first_name or ""
    username = query.from_user.username or ""
    user_is_admin = is_admin_sync(user_id)
    await run_db(save_user, user_id, first_name, username)

    if data == "noop":
        await query.answer()
        return

    if data.startswith("adm:"):
        if not user_is_admin:
            await query.answer("⛔ Unauthorized!", show_alert=True)
            return
        if not _has_adm_callback_perm(user_id, data):
            await query.answer("⛔ Unauthorized! You do not have permission for this action.", show_alert=True)
            return

    if data == "fj_check":
        chats = get_force_join_chats()
        if not chats:
            await query.answer("✅ Access granted!", show_alert=True)
            try:
                await query.edit_message_text("✅ Verification complete! Type /start to continue.")
            except Exception:
                pass
            return
        ok, _missing = await check_user_joined_all(context.bot, user_id, chats)
        if ok:
            now_fj = time.time()
            if len(_FORCE_JOIN_CACHE) >= _FORCE_JOIN_CACHE_MAX:
                _prune_ts_cache(_FORCE_JOIN_CACHE, _FORCE_JOIN_CACHE_TTL, _FORCE_JOIN_CACHE_MAX - 1, now=now_fj)
            _FORCE_JOIN_CACHE[user_id] = now_fj
            await query.answer("✅ Verified! You can now use the bot.", show_alert=True)
            try:
                await query.edit_message_text(
                    "✅ <b>Verification Complete!</b>\n\nYou can now use the bot. Tap /start to continue.",
                    parse_mode="HTML"
                )
            except Exception:
                pass
        else:
            await query.answer(
                "❌ You haven't joined all channels/groups yet. Please join and try again.",
                show_alert=True
            )
        return

    if not user_is_admin and data != "fj_check":
        if await run_db(is_user_banned_sync, user_id):
            try:
                await query.answer(
                    "🚫 You are banned.\n\nPlease contact support to resolve this.",
                    show_alert=True,
                )
            except Exception:
                pass
            return

    _skip_fj = user_is_admin or data.startswith("adm:") or data.startswith("fj_")
    if not _skip_fj and is_force_join_enabled():
        chats = get_force_join_chats()
        if chats:
            ok = await is_user_force_join_ok(context.bot, user_id)
            if not ok:
                try:
                    await query.edit_message_text(
                        FORCE_JOIN_TEXT,
                        reply_markup=build_force_join_keyboard(chats),
                        parse_mode="HTML",
                        link_preview_options=LinkPreviewOptions(is_disabled=True),
                    )
                except Exception:
                    try:
                        await query.message.reply_text(
                            FORCE_JOIN_TEXT,
                            reply_markup=build_force_join_keyboard(chats),
                            parse_mode="HTML",
                            link_preview_options=LinkPreviewOptions(is_disabled=True),
                        )
                    except Exception:
                        pass
                return

    if data == "back_to_services":
        await query.answer()
        kbd, msg = get_services_keyboard()
        if not kbd:
            await query.edit_message_text(msg)
        else:
            await query.edit_message_text(msg, reply_markup=kbd, parse_mode="HTML")

    elif data == "usr:withdraw":
        withdraw_on = get_setting("withdraw_enabled", "true") == "true"
        if not withdraw_on:
            await query.answer("❌ Withdraw feature is disabled.", show_alert=True)
            return

        bal = await run_db(get_user_balance_sync, user_id)
        min_w = float(get_setting("min_withdraw_amount", "50") or 50)

        if bal < min_w:
            await query.answer(
                f"❌ ব্যালেন্স কম! Minimum: {fmt_num(min_w)} ৳। আপনার: {fmt_num(bal)} ৳।",
                show_alert=True
            )
            return

        await query.answer()
        methods = await run_db(get_withdraw_methods_sync)
        if not methods:
            await query.edit_message_text("❌ No withdraw methods available.")
            return

        buttons = []
        for m in methods:
            buttons.append([create_button(m, callback_data=f"usr:w_method:{m}", style="primary")])
        await query.edit_message_text("💳 **SELECT WITHDRAW METHOD:**", reply_markup=InlineKeyboardMarkup(buttons), parse_mode="Markdown")

    elif data == "adm:w_settings":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text_msg, kbd = build_withdraw_settings_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:r_bonus_settings":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text_msg, kbd = build_ranking_bonus_settings_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:refer_settings":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text_msg, kbd = build_refer_settings_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:extra_back":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text_msg, kbd = build_extra_settings_view(user_id=user_id)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:fj_settings":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text_msg, kbd = build_force_join_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:fj_toggle":
        if not user_is_admin: await query.answer(); return
        curr = is_force_join_enabled()
        new_val = "false" if curr else "true"
        await run_db(set_setting, "force_join_enabled", new_val)
        await query.answer(
            f"Force Join is now {'enabled' if new_val == 'true' else 'disabled'}!",
            show_alert=True
        )
        text_msg, kbd = build_force_join_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:fj_rem_list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        chats = get_force_join_chats()
        buttons = []
        for i, ch in enumerate(chats):
            buttons.append([create_button(
                ch.get('title', 'N/A'),
                callback_data=f"adm:fj_rem:{i}",
                style="danger",
                icon_custom_emoji_id="6267000941547885720"
            )])
        buttons.append([create_button("Back", callback_data="adm:fj_settings", style="primary", icon_custom_emoji_id="5456187398977247949")])
        await query.edit_message_text("Select a channel/group to remove:", reply_markup=InlineKeyboardMarkup(buttons))

    elif data.startswith("adm:fj_rem:"):
        if not user_is_admin: await query.answer(); return
        idx = int(data.split(":", 2)[2])
        chats = get_force_join_chats()
        if 0 <= idx < len(chats):
            removed = chats.pop(idx)
            await run_db(set_force_join_chats, chats)
            await query.answer(f"Removed {removed.get('title', 'N/A')}!", show_alert=True)
        text_msg, kbd = build_force_join_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:panel_back":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        total_users = len(await run_db(get_all_users))
        role_lbl = get_admin_role_label(user_id)
        panel_text = (
            f"**ADMIN PANEL**\n\n"
            f"🎭 Role: **{role_lbl}**\n"
            f"⚙️ DB Mode: **{CURRENT_DB_MODE}**\n"
            f"👥 Total Users: `{total_users}`"
        )
        await _reply_with_emoji_fallback(
            query.message,
            lambda prem: (panel_text, get_admin_keyboard(use_premium=prem, user_id=user_id)),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:live:page:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        filter_mode = parts[3] if len(parts) > 3 else "all"
        try:
            page = int(parts[4]) if len(parts) > 4 else 1
        except ValueError:
            page = 1
        try:
            live_events = await run_db(get_live_receiver_events_sync, filter_mode)
            status = await _edit_with_emoji_fallback(
                query,
                lambda prem: build_live_receivers_view(filter_mode, page, use_premium=prem, events=live_events),
                parse_mode="HTML",
                link_preview_options=LinkPreviewOptions(is_disabled=True),
            )
            await query.answer("Already up to date!" if status == "not_modified" else "Updated!")
        except Exception as e:
            logger.warning(f"adm:live:page error: {e}")
            await query.answer()

    elif data.startswith("adm:live:summary:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        filter_mode = parts[3] if len(parts) > 3 else "all"
        try:
            page = int(parts[4]) if len(parts) > 4 else 1
        except ValueError:
            page = 1
        try:
            live_events = await run_db(get_live_receiver_events_sync, filter_mode)
            status = await _edit_with_emoji_fallback(
                query,
                lambda prem: build_live_receivers_summary_view(filter_mode, page, use_premium=prem, events=live_events),
                parse_mode="HTML",
                link_preview_options=LinkPreviewOptions(is_disabled=True),
            )
            await query.answer("Already up to date!" if status == "not_modified" else "Updated!")
        except Exception as e:
            logger.warning(f"adm:live:summary error: {e}")
            await query.answer()

    elif data == "adm:usr:manager":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_user_manager_view(use_premium=prem, user_id=user_id),
            parse_mode="Markdown",
        )

    elif data == "adm:usr:control":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_user_control_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:usr:all:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        parts = data.split(":", 4)
        sort_mode = parts[3] if len(parts) > 3 else "recent"
        try:
            page = int(parts[4]) if len(parts) > 4 else 1
        except ValueError:
            page = 1
        users_list = await run_db(get_users_ordered_sync, sort_mode)
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_all_users_view(sort_mode, page, use_premium=prem, users=users_list),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:usr:banned:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        parts = data.split(":", 3)
        try:
            page = int(parts[3]) if len(parts) > 3 else 1
        except ValueError:
            page = 1
        users_list = await run_db(get_banned_users_list_sync)
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_banned_users_view(page, use_premium=prem, users=users_list),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:usr:inactive:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        parts = data.split(":", 4)
        win = parts[3] if len(parts) > 3 else "7d"
        try:
            page = int(parts[4]) if len(parts) > 4 else 1
        except ValueError:
            page = 1
        users_list = await run_db(get_inactive_users_list_sync, win)
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_inactive_users_view(win, page, use_premium=prem, users=users_list),
            parse_mode="Markdown",
        )

    elif data == "adm:usr:autoban":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_autoban_settings_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data == "adm:usr:ab:tog_abuse":
        if not user_is_admin: await query.answer(); return
        curr = is_abuse_autoban_enabled()
        new_val = "false" if curr else "true"
        await run_db(set_setting, "autoban_abuse_enabled", new_val)
        await query.answer(
            f"Abuse Auto-Ban {'enabled' if new_val == 'true' else 'disabled'}!",
            show_alert=True,
        )
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_autoban_settings_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data == "adm:usr:ab:tog_inact":
        if not user_is_admin: await query.answer(); return
        curr = is_inactive_autoban_enabled()
        new_val = "false" if curr else "true"
        await run_db(set_setting, "autoban_inactive_enabled", new_val)
        await query.answer(
            f"Inactive Auto-Ban {'enabled' if new_val == 'true' else 'disabled'}!",
            show_alert=True,
        )
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_autoban_settings_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data == "adm:usr:ab:run_now":
        if not user_is_admin: await query.answer(); return
        if not is_inactive_autoban_enabled():
            await query.answer("❌ Enable Inactive Auto-Ban first before running sweep.", show_alert=True)
            return
        banned_list = await run_db(run_inactive_autoban_sweep_sync)
        for b in banned_list:
            await _send_banned_message(context.bot, b["uid"])
        await query.answer(f"⚡ Auto-banned {len(banned_list)} inactive user(s)!", show_alert=True)
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_autoban_settings_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:usr:view:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        parts = data.split(":", 4)
        target_uid = int(parts[3])
        back_tok = parts[4] if len(parts) > 4 else "c"
        back_cb = _decode_usr_back(back_tok)
        user_data = await run_db(search_user_sync, str(target_uid))
        if not user_data:
            await query.answer("❌ User not found!", show_alert=True)
            return
        refer_count = await run_db(get_user_refer_count_sync, target_uid)
        text, kbd = _build_user_detail_view(target_uid, user_data, back_cb=back_cb, refer_count=refer_count)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data == "adm:usr:stats":
        if not user_is_admin: await query.answer(); return
        await query.answer("Calculating stats...", show_alert=False)
        text_msg, kbd = await run_db(build_stats_view)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:usr:export":
        if not user_is_admin: await query.answer(); return
        await query.answer("Exporting, please wait...", show_alert=True)

        users = await run_db(get_all_users_data_sync)
        if not users:
            await query.edit_message_text("❌ No users found to export.")
            return

        json_str = json.dumps(users, indent=4, default=str)
        file_obj = io.BytesIO(json_str.encode('utf-8'))
        file_obj.name = f"users_export_{int(time.time())}.json"

        await context.bot.send_document(
            chat_id=query.from_user.id,
            document=file_obj,
            caption=f"✅ Exported {len(users)} users successfully!"
        )
        await _edit_with_emoji_fallback(
            query,
            lambda prem: ("✅ Export completed. Check the file sent above.", build_user_manager_view(use_premium=prem, user_id=user_id)[1]),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:usr:ban:") or data.startswith("adm:usr:unban:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        action = parts[2]
        target_uid = int(parts[3])
        back_tok = parts[4] if len(parts) > 4 else "c"
        back_cb = _decode_usr_back(back_tok)
        if is_admin_sync(target_uid):
            await query.answer("❌ Cannot ban/unban an admin!", show_alert=True)
            return
        is_banning = (action == "ban")
        reason = "Manually banned by admin" if is_banning else ""
        ok = await run_db(set_user_banned_sync, target_uid, is_banning, reason)
        if ok and is_banning:
            await _send_banned_message(context.bot, target_uid)
        await query.answer(
            "✅ User banned!" if is_banning else "✅ User unbanned!",
            show_alert=True,
        )
        user_data = await run_db(search_user_sync, str(target_uid))
        if user_data:
            refer_count = await run_db(get_user_refer_count_sync, target_uid)
            text, kbd = _build_user_detail_view(target_uid, user_data, back_cb=back_cb, refer_count=refer_count)
            try:
                await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")
            except Exception:
                pass

    elif data.startswith("adm:usr:release:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        target_uid = int(parts[3])
        back_tok = parts[4] if len(parts) > 4 else "c"
        back_cb = _decode_usr_back(back_tok)
        await query.answer("Releasing numbers...", show_alert=False)
        count = await run_db(release_user_allocations_sync, target_uid)
        await query.answer(f"✅ Released {count} numbers.", show_alert=True)
        user_data = await run_db(search_user_sync, str(target_uid))
        if user_data:
            refer_count = await run_db(get_user_refer_count_sync, target_uid)
            text, kbd = _build_user_detail_view(target_uid, user_data, back_cb=back_cb, refer_count=refer_count)
            try:
                await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")
            except Exception:
                pass

    elif data == "adm:w_del_m_list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        methods = await run_db(get_withdraw_methods_sync)
        buttons = []
        for m in methods:
            buttons.append([create_button(f"Delete {m}", callback_data=f"adm:w_del_m:{m}", style="danger", icon_custom_emoji_id="6267000941547885720")])
        buttons.append([create_button("Back", callback_data="adm:w_settings", style="primary", icon_custom_emoji_id="5456187398977247949")])
        await query.edit_message_text("Select payment method to remove:", reply_markup=InlineKeyboardMarkup(buttons))

    elif data.startswith("adm:w_del_m:"):
        if not user_is_admin: await query.answer(); return
        m_name = data.split(":", 2)[2]
        await run_db(delete_withdraw_method_sync, m_name)
        await query.answer(f"Method {m_name} removed!", show_alert=True)
        text_msg, kbd = build_withdraw_settings_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("adm:w_page:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        page = int(data.split(":", 2)[2])
        text_msg, kbd = await run_db(build_admin_withdraw_requests_view, page)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("adm:w_view:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        req_id = int(data.split(":", 2)[2])
        text_msg, kbd = await run_db(build_withdraw_detail_view, req_id)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:w_app:"):
        if not user_is_admin: await query.answer(); return
        req_id = int(data.split(":", 2)[2])
        req = await run_db(get_withdraw_request_by_id_sync, req_id)
        if not req or req["status"] != "pending":
            await query.answer("Already processed!", show_alert=True)
            return

        ok = await run_db(atomic_transition_withdraw_status_sync, req_id, "pending", "approved", "")
        if not ok:
            await query.answer("Already processed!", show_alert=True)
            return

        await query.answer("Approved!", show_alert=True)

        if get_setting("refer_enabled", "true") == "true":
            try:
                referrer_id = await run_db(get_user_referrer_sync, req["user_id"])
                if referrer_id and referrer_id != req["user_id"]:
                    try:
                        pct = float(get_setting("refer_commission_percent", "5") or 5)
                    except Exception:
                        pct = 5.0
                    if pct > 0:
                        commission = float(req["amount"]) * pct / 100.0
                        if commission > 0:
                            ok_c = await run_db(add_refer_commission_sync, referrer_id, commission)
                            if ok_c:
                                try:
                                    notif = (
                                        "🎁 <b>REFERRAL COMMISSION EARNED!</b>\n\n"
                                        f"Your referred user withdrew <b>{fmt_num(req['amount'])} ৳</b>.\n"
                                        f"You earned <b>{fmt_num(commission)} ৳</b> "
                                        f"({fmt_num(pct)}% commission)!\n\n"
                                        "💰 Amount added to your balance."
                                    )
                                    await context.bot.send_message(
                                        chat_id=referrer_id, text=notif, parse_mode="HTML"
                                    )
                                except Exception as e:
                                    logger.error(f"refer notif failed: {e}")
            except Exception as e:
                logger.error(f"refer commission error: {e}")

        user_msg = (
            "✅ <b>WITHDRAWAL APPROVED</b>\n\n"
            f"Your withdrawal request of <b>{fmt_num(req['amount'])} ৳</b> via <b>{html.escape(req['method'])}</b> has been approved!\n"
            f"Account / Wallet: <code>{html.escape(req['wallet_number'])}</code>"
        )
        try:
            await context.bot.send_message(chat_id=req["user_id"], text=user_msg, parse_mode="HTML")
        except Exception as e:
            logging.error(f"Failed approval notification: {e}")

        text_msg, kbd = build_withdraw_detail_view(req_id)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="HTML")

    elif data == "adm:ctrl:list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_admin_control_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:ctrl:view:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        target_uid = int(data.split(":", 3)[3])
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_admin_detail_view(target_uid, use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:ctrl:preset:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        target_uid = int(parts[3])
        role_key = parts[4]
        if target_uid == ADMIN_ID:
            await query.answer("🔒 Main Owner permissions cannot be changed!", show_alert=True)
            return
        await run_db(apply_admin_role_preset_sync, target_uid, role_key)
        lbl = ADMIN_ROLE_PRESETS.get(role_key, {}).get("label", role_key)
        await query.answer(f"Role set to {lbl}!")
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_admin_detail_view(target_uid, use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:ctrl:perm:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        target_uid = int(parts[3])
        perm_key = parts[4]
        if target_uid == ADMIN_ID:
            await query.answer("🔒 Main Owner permissions cannot be changed!", show_alert=True)
            return
        new_state = await run_db(toggle_admin_perm_sync, target_uid, perm_key)
        await query.answer(f"{perm_key}: {'Enabled' if new_state else 'Disabled'}")
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_admin_detail_view(target_uid, use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:add:role:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        target_uid = int(parts[3])
        role_key = parts[4]
        if target_uid != ADMIN_ID:
            await run_db(apply_admin_role_preset_sync, target_uid, role_key)
        lbl = ADMIN_ROLE_PRESETS.get(role_key, {}).get("label", role_key)
        await query.answer(f"Role set to {lbl}!", show_alert=True)
        if role_key == "custom":
            await _edit_with_emoji_fallback(
                query,
                lambda prem: build_admin_detail_view(target_uid, use_premium=prem),
                parse_mode="Markdown",
            )
        else:
            await _edit_with_emoji_fallback(
                query,
                lambda prem: build_admin_control_view(use_premium=prem),
                parse_mode="Markdown",
            )

    elif data.startswith("adm:delconf:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        target_uid = int(data.split(":", 2)[2])
        if target_uid == ADMIN_ID:
            await query.answer("❌ Main Owner cannot be removed!", show_alert=True)
            return
        admins = await run_db(get_all_admins_sync)
        target_adm = next((a for a in admins if a["user_id"] == target_uid), None)
        target_name = target_adm["name"] if target_adm else "Admin"
        text = (
            f"⚠️ **CONFIRMATION**\n\nRemove admin **{escape_md(target_name)}** (`{target_uid}`)?"
        )
        await _edit_with_emoji_fallback(
            query,
            lambda prem: (
                text,
                InlineKeyboardMarkup([[
                    _admin_inline_btn("YES, REMOVE", callback_data=f"adm:del:{target_uid}", style="danger", emoji_id="5424998570539373838", fallback_emoji="✅", use_premium=prem),
                    _admin_inline_btn("CANCEL", callback_data=f"adm:ctrl:view:{target_uid}", style="primary", emoji_id="5456187398977247949", fallback_emoji="◀️", use_premium=prem),
                ]]),
            ),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:del:"):
        if not user_is_admin: await query.answer(); return
        target_uid = int(data.split(":", 2)[2])
        if target_uid == ADMIN_ID:
            await query.answer("❌ Cannot remove!", show_alert=True)
            return
        success = await run_db(delete_admin_sync, target_uid)
        await query.answer("Removed!" if success else "Failed.", show_alert=True)
        await _edit_with_emoji_fallback(
            query,
            lambda prem: build_admin_control_view(use_premium=prem),
            parse_mode="Markdown",
        )

    elif data.startswith("adm:setqty:"):
        if not user_is_admin: await query.answer(); return
        qty_val = data.split(":", 2)[2]
        await run_db(set_setting, "number_quantity", qty_val)
        await query.answer(f"Set to {qty_val}!", show_alert=True)
        text_msg, kbd = build_number_quantity_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data in ("adm:toggle:show_msg", "adm:toggle:country_count", "adm:toggle:show_dev",
                  "adm:toggle:withdraw", "adm:toggle:ranking_bonus", "adm:toggle:refer"):
        if not user_is_admin: await query.answer(); return
        setting_map = {
            "adm:toggle:show_msg": ("show_message", "true", "Show Message"),
            "adm:toggle:country_count": ("show_country_count", "false", "Number Count"),
            "adm:toggle:show_dev": ("show_developer", "true", "Developer Info"),
            "adm:toggle:withdraw": ("withdraw_enabled", "true", "Withdraw system"),
            "adm:toggle:ranking_bonus": ("ranking_bonus_enabled", "true", "Ranking Bonus"),
            "adm:toggle:refer": ("refer_enabled", "true", "Refer System"),
        }
        key, default_val, label = setting_map[data]
        curr_val = get_setting(key, default_val)
        new_val = "false" if curr_val == "true" else "true"
        await run_db(set_setting, key, new_val)
        status_text = "enabled" if new_val == "true" else "disabled"
        await query.answer(f"{label} is now {status_text}!", show_alert=True)
        if data == "adm:toggle:withdraw":
            text_msg, kbd = build_withdraw_settings_view()
        elif data == "adm:toggle:ranking_bonus":
            text_msg, kbd = build_ranking_bonus_settings_view()
        elif data == "adm:toggle:refer":
            text_msg, kbd = build_refer_settings_view()
        else:
            text_msg, kbd = build_extra_settings_view(user_id=user_id)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:toggle:otp_format":
        if not user_is_admin: await query.answer(); return
        curr = get_setting("otp_group_format", "regular")
        new_val = "premium" if curr != "premium" else "regular"
        await run_db(set_setting, "otp_group_format", new_val)
        await query.answer(
            f"OTP format set to {new_val.upper()}!",
            show_alert=True,
        )
        text_msg, kbd = build_extra_settings_view(user_id=user_id)
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:srv:list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text, kbd = build_admin_services_view()
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:srv:view:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service = _resolve_srv_token(data.split(":", 3)[3])
        text, kbd = await run_db(build_service_manage_view, service)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:srv:delconf:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service = _resolve_srv_token(data.split(":", 3)[3])
        srv_tok = _make_srv_token(service)
        kbd = InlineKeyboardMarkup([
            [
                create_button("Yes, Delete", callback_data=f"adm:srv:del:{srv_tok}", style="danger", icon_custom_emoji_id="5422557736330106570"),
                create_button("Cancel", callback_data=f"adm:srv:view:{srv_tok}", style="primary", icon_custom_emoji_id="5456187398977247949"),
            ]
        ])
        await query.edit_message_text(
            f"⚠️ <b>CONFIRM DELETE SERVICE</b>\n\n"
            f"Are you sure you want to delete service <b>{safe_html_escape(service)}</b> and all of its countries and numbers?",
            reply_markup=kbd, parse_mode="HTML",
        )

    elif data.startswith("adm:srv:del:"):
        if not user_is_admin: await query.answer(); return
        service = _resolve_srv_token(data.split(":", 3)[3])
        await run_db(delete_service_db, service)
        await query.answer("Service deleted!", show_alert=True)
        text, kbd = build_admin_services_view()
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:c:v:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        text, kbd = await run_db(build_country_manage_view, service, country)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:c:ed:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        text, kbd = await run_db(build_country_edit_view, service, country)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:c:cc:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        if len(parts) >= 5:
            cc_digit = parts[3]
            service, country = _resolve_sc_token(parts[4])
            await run_db(set_setting, f"cc_len:{service}:{country}", cc_digit)
            await query.answer(f"Country Code Digit set to {cc_digit}!", show_alert=True)
            text, kbd = build_country_edit_view(service, country)
            try:
                await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")
            except Exception:
                pass
        else:
            await query.answer()

    elif data.startswith("adm:c:dc:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        sc_tok = _make_sc_token(service, country)
        kbd = InlineKeyboardMarkup([
            [
                create_button("Yes, Delete", callback_data=f"adm:c:dl:{sc_tok}", style="danger", icon_custom_emoji_id="5422557736330106570"),
                create_button("Cancel", callback_data=f"adm:c:v:{sc_tok}", style="primary", icon_custom_emoji_id="5456187398977247949"),
            ]
        ])
        await query.edit_message_text(
            f"⚠️ <b>CONFIRM DELETE COUNTRY</b>\n\n"
            f"Are you sure you want to delete <b>{safe_html_escape(country)}</b> from <b>{safe_html_escape(service)}</b> and all of its numbers?",
            reply_markup=kbd, parse_mode="HTML",
        )

    elif data.startswith("adm:c:dl:"):
        if not user_is_admin: await query.answer(); return
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        await run_db(delete_country_db, service, country)
        await query.answer("Country deleted!", show_alert=True)
        text, kbd = build_service_manage_view(service)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:c:cconf:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        sc_tok = _make_sc_token(service, country)
        avail = SERVICES_CACHE.get(service, {}).get(country, 0)
        kbd = InlineKeyboardMarkup([
            [
                create_button("Yes, Clear Stock", callback_data=f"adm:c:cdo:{sc_tok}", style="danger", icon_custom_emoji_id="5422557736330106570"),
                create_button("Cancel", callback_data=f"adm:c:v:{sc_tok}", style="primary", icon_custom_emoji_id="5456187398977247949"),
            ]
        ])
        await query.edit_message_text(
            f"⚠️ <b>CONFIRM CLEAR STOCK</b>\n\n"
            f"Are you sure you want to clear all <b>{avail}</b> available unallocated numbers for "
            f"<b>{safe_html_escape(country)}</b> in <b>{safe_html_escape(service)}</b>?\n\n"
            f"<i>Note: Clearing stock will automatically pause this country.</i>",
            reply_markup=kbd, parse_mode="HTML",
        )

    elif data.startswith("adm:c:cdo:"):
        if not user_is_admin: await query.answer(); return
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        cleared = await run_db(clear_country_stock_db, service, country)
        await query.answer(f"Cleared {cleared} numbers! Country auto-paused.", show_alert=True)
        text, kbd = await run_db(build_country_manage_view, service, country)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("adm:c:togp:"):
        if not user_is_admin: await query.answer(); return
        service, country = _resolve_sc_token(data.split(":", 3)[3])
        currently_paused = is_country_paused_sync(service, country)
        if currently_paused:
            avail = SERVICES_CACHE.get(service, {}).get(country, 0)
            if avail <= 0:
                await query.answer("❌ Cannot resume! No available numbers in stock. Add numbers first.", show_alert=True)
                return
            await run_db(set_country_paused_sync, service, country, False)
            await query.answer("▶️ Country resumed!", show_alert=True)
        else:
            await run_db(set_country_paused_sync, service, country, True)
            await query.answer("⏸️ Country paused!", show_alert=True)
        text, kbd = await run_db(build_country_manage_view, service, country)
        try:
            await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")
        except Exception:
            pass

    elif data.startswith("adm:cnt:delli:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service = _resolve_srv_token(data.split(":", 3)[3])
        cnts = get_admin_services_summary().get(service, {})
        buttons = []
        for cnt in cnts.keys():
            buttons.append([create_button(f"Delete {cnt}", callback_data=f"adm:cnt:del:{_cb_clean(service)}:{_cb_clean(cnt)}", style="danger", icon_custom_emoji_id="5422557736330106570")])
        buttons.append([create_button("Back", callback_data=f"adm:srv:view:{_make_srv_token(service)}", style="danger", icon_custom_emoji_id="5456187398977247949")])
        await query.edit_message_text(
            f"Select country to delete from <b>{safe_html_escape(service)}</b>:",
            reply_markup=InlineKeyboardMarkup(buttons), parse_mode="HTML"
        )

    elif data.startswith("adm:cnt:del:"):
        if not user_is_admin: await query.answer(); return
        parts = data.split(":", 4)
        if len(parts) >= 5:
            service = _resolve_full_key(parts[3], list(SERVICES_CACHE.keys()))
            country = _resolve_full_key(parts[4], list(SERVICES_CACHE.get(service, {}).keys()))
            await run_db(delete_country_db, service, country)
            await query.answer(f"Deleted!", show_alert=True)
            text, kbd = build_service_manage_view(service)
            await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")
        else:
            await query.answer()

    elif data.startswith("adm:pay:mng:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        service = _resolve_srv_token(data.split(":", 3)[3])
        text, kbd = await run_db(build_payout_manage_view, service)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="HTML")

    elif data == "adm:api:list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text, kbd = build_api_panels_view()
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:cliemoji:list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        text_msg, kbd = build_cli_emojis_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data == "adm:cliemoji:del_list":
        if not user_is_admin: await query.answer(); return
        await query.answer()
        keys = [k for k in SETTINGS_CACHE.keys() if k.startswith("cli_emoji:")]
        if not keys:
            await query.answer("No CLI emojis to delete.", show_alert=True)
            text_msg, kbd = build_cli_emojis_view()
            await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")
            return
        buttons = []
        for k in keys:
            cli_name = k.split(":", 1)[1]
            buttons.append([create_button(
                f"Delete {cli_name}",
                callback_data=f"adm:cliemoji:del:{cli_name}",
                style="danger",
                icon_custom_emoji_id="5422557736330106570"
            )])
        buttons.append([create_button("Back", callback_data="adm:cliemoji:list", style="primary", icon_custom_emoji_id="5456187398977247949")])
        await query.edit_message_text("Select CLI to remove:", reply_markup=InlineKeyboardMarkup(buttons))

    elif data.startswith("adm:cliemoji:del:"):
        if not user_is_admin: await query.answer(); return
        cli_name = data.split(":", 3)[3]
        try:
            await run_db(set_setting, f"cli_emoji:{cli_name}", "")
            supabase.table("settings").delete().eq("key", f"cli_emoji:{cli_name}").execute()
            SETTINGS_CACHE.pop(f"cli_emoji:{cli_name}", None)
        except Exception as e:
            logger.error(f"cli emoji delete error: {e}")
        await query.answer(f"Deleted emoji for {cli_name}!", show_alert=True)
        text_msg, kbd = build_cli_emojis_view()
        await query.edit_message_text(text_msg, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("adm:api:view:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        panel_id = data.split(":", 3)[3]
        text, kbd = await run_db(build_panel_manage_view, panel_id)
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("adm:api:test:"):
        if not user_is_admin: await query.answer(); return
        await query.answer("Fetching...")
        panel_id = data.split(":", 3)[3]
        p = await run_db(get_api_panel_sync, panel_id)
        if not p:
            await query.edit_message_text("⚠️ Panel not found.")
            return

        if get_panel_type(p) == "augestel":
            try:
                cfg = json.loads(p.get("mapping_json") or "{}")
            except Exception:
                cfg = {}
            await _augestel_close_session(str(panel_id))
            ok, status = await _augestel_login(str(panel_id), p, cfg)
            if not ok:
                AUGESTEL_PANEL_STATUS[str(panel_id)] = status
                kbd = InlineKeyboardMarkup([
                    [create_button("Back", callback_data=f"adm:api:view:{panel_id}", style="primary")]
                ])
                await query.edit_message_text(
                    f"❌ <b>Login Failed</b>\n\n<code>{html.escape(status)}</code>",
                    reply_markup=kbd, parse_mode="HTML"
                )
                return
            items, fetch_status = await fetch_augestel_panel_data(str(panel_id), cfg)
            AUGESTEL_PANEL_STATUS[str(panel_id)] = fetch_status
            preview = ""
            for i, it in enumerate(items[:3], 1):
                otp_code = extract_otp(it["message"])
                dt_preview = f" | 📅 {html.escape(str(it.get('dt', ''))[:25])}" if it.get('dt') else ""
                preview += (
                    f"\n<b>{i}.</b> 📱 <code>{html.escape(it['num'])}</code>{dt_preview}\n"
                    f"   💬 <code>{html.escape(it['message'][:150])}</code>\n"
                    f"   🔐 OTP: <code>{html.escape(otp_code)}</code>\n"
                )
            if not preview:
                preview = f"\n<i>No OTP rows found.</i>\n<b>Debug info:</b>\n• Email: <code>{html.escape(str(cfg.get('email', '')))}</code>\n• Check credentials and that the panel has messages in the last 1 day.\n"
            kbd = InlineKeyboardMarkup([
                [create_button("Back", callback_data=f"adm:api:view:{panel_id}", style="primary")]
            ])
            await query.edit_message_text(
                f"✅ <b>Login OK</b>\n"
                f"Status: <code>{html.escape(fetch_status)}</code>\n"
                f"Total fetched: <b>{len(items)}</b>\n"
                f"{preview}",
                reply_markup=kbd, parse_mode="HTML"
            )
            return

        if get_panel_type(p) == "captcha":
            try:
                cfg = json.loads(p.get("mapping_json") or "{}")
            except Exception:
                cfg = {}

            old = CAPTCHA_SESSIONS.pop(str(panel_id), None)
            if old:
                try: await old["client"].aclose()
                except Exception: pass

            ok, status = await attempt_captcha_login(str(panel_id), p, cfg)
            if not ok:
                CAPTCHA_PANEL_STATUS[str(panel_id)] = status
                kbd = InlineKeyboardMarkup([
                    [create_button("Back", callback_data=f"adm:api:view:{panel_id}", style="primary")]
                ])
                await query.edit_message_text(
                    f"❌ <b>Login Failed</b>\n\n<code>{html.escape(status)}</code>",
                    reply_markup=kbd, parse_mode="HTML"
                )
                return

            items, fetch_status = await fetch_captcha_panel_data(str(panel_id), cfg)
            CAPTCHA_PANEL_STATUS[str(panel_id)] = fetch_status

            preview = ""
            for i, it in enumerate(items[:3], 1):
                otp_code = extract_otp(it["message"])
                dt_preview = f" | 📅 {html.escape(str(it.get('dt', ''))[:25])}" if it.get('dt') else ""
                preview += (
                    f"\n<b>{i}.</b> 📱 <code>{html.escape(it['num'])}</code>{dt_preview}\n"
                    f"   💬 <code>{html.escape(it['message'][:150])}</code>\n"
                    f"   🔐 OTP: <code>{html.escape(otp_code)}</code>\n"
                )
            if not preview:
                preview = (
                    f"\n<i>No OTP rows found.</i>\n"
                    f"<b>Debug info:</b>\n"
                    f"• Num idx: {cfg.get('num_col_idx')} | Msg idx: {cfg.get('msg_col_idx')}\n"
                    f"• Date idx: {cfg.get('dt_col_idx')}\n"
                    f"• Check that the Message Link is the actual AJAX endpoint.\n"
                    f"• Check the column indexes match the panel's table.\n"
                )
            kbd = InlineKeyboardMarkup([
                [create_button("Back", callback_data=f"adm:api:view:{panel_id}", style="primary")]
            ])
            await query.edit_message_text(
                f"✅ <b>Login OK</b>\n"
                f"Status: <code>{html.escape(fetch_status)}</code>\n"
                f"Total fetched: <b>{len(items)}</b>\n"
                f"{preview}",
                reply_markup=kbd, parse_mode="HTML"
            )
            return

        try:
            async with httpx.AsyncClient(
                timeout=10.0,
                follow_redirects=True,
                headers={"User-Agent": "Mozilla/5.0 (compatible; OTPBot/1.0)"},
            ) as client:
                if p.get("mapping_json"):
                    test_headers = {"Accept": "application/json"}
                    if p.get("token"):
                        test_headers["Authorization"] = f"Bearer {p['token']}"
                    res = await client.get(p["url"], headers=test_headers)
                else:
                    res = await client.get(p["url"])
            body_preview = res.text[:1500] if res.text else "(empty)"
            parsed_info = ""
            try:
                j = res.json()
                if p.get("mapping_json"):
                    m = json.loads(p["mapping_json"])
                    items = apply_custom_mapping(j, m)
                    parsed_info = f"\n\n🧩 Custom parse → {len(items)} item(s)"
                    if items:
                        first = items[0]
                        parsed_info += (
                            f"\nFirst: num={first.get('num')}, "
                            f"dt={str(first.get('dt'))[:30]}, "
                            f"payout={first.get('payout')}"
                        )
                else:
                    parsed_info = f"\n\nKeys: {list(j.keys()) if isinstance(j, dict) else type(j).__name__}"
            except Exception as e:
                parsed_info = f"\n\n⚠️ JSON parse failed: {e}"

            text = (
                f"🧪 <b>TEST FETCH — {html.escape(p['name'])}</b>\n"
                f"Status: <code>{res.status_code}</code>\n"
                f"URL: <code>{html.escape(p['url'][:200])}</code>\n"
                f"Body preview:\n<pre>{html.escape(body_preview[:1200])}</pre>"
                f"{html.escape(parsed_info)}"
            )
            kbd = InlineKeyboardMarkup([
                [create_button("Back to Panel", callback_data=f"adm:api:view:{panel_id}", style="primary")]
            ])
            await query.edit_message_text(text[:4000], reply_markup=kbd, parse_mode="HTML")
        except Exception as e:
            await query.edit_message_text(
                f"❌ Fetch failed: <code>{html.escape(str(e))}</code>",
                parse_mode="HTML"
            )

    elif data.startswith("adm:api:relogin:"):
        if not user_is_admin: await query.answer(); return
        panel_id = data.split(":", 3)[3]
        p = await run_db(get_api_panel_sync, panel_id)
        if p and get_panel_type(p) == "augestel":
            await _augestel_close_session(str(panel_id))
            AUGESTEL_PANEL_STATUS[str(panel_id)] = "🔄 Re-login triggered"
            await query.answer("Session cleared. Will re-login shortly.", show_alert=True)
            text, kbd = build_panel_manage_view(str(panel_id))
            await query.edit_message_text(text, reply_markup=kbd, parse_mode="Markdown")
            return
        old = CAPTCHA_SESSIONS.pop(str(panel_id), None)
        if old:
            try: await old["client"].aclose()
            except Exception: pass
        CAPTCHA_PANEL_STATUS[str(panel_id)] = "🔄 Re-login triggered"
        await query.answer("Session cleared. Will re-login shortly.", show_alert=True)
        text, kbd = build_panel_manage_view(str(panel_id))
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("adm:api:delconf:"):
        if not user_is_admin: await query.answer(); return
        await query.answer()
        panel_id = data.split(":", 3)[3]
        p = await run_db(get_api_panel_sync, panel_id)
        if p:
            text = f"⚠️ Delete panel **'{escape_md(p['name'])}'**?"
            kbd = InlineKeyboardMarkup([
                [create_button("YES", callback_data=f"adm:api:del:{panel_id}", style="danger", icon_custom_emoji_id="5424998570539373838"),
                 create_button("CANCEL", callback_data=f"adm:api:view:{panel_id}", style="primary", icon_custom_emoji_id="6267000941547885720")]
            ])
            await query.edit_message_text(text, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("adm:api:del:"):
        if not user_is_admin: await query.answer(); return
        panel_id = data.split(":", 3)[3]
        await run_db(delete_api_panel_sync, panel_id)
        await query.answer("Panel deleted!", show_alert=True)
        text, kbd = build_api_panels_view()
        await query.edit_message_text(text, reply_markup=kbd, parse_mode="Markdown")

    elif data.startswith("srv_"):
        await query.answer()
        clean_service = data.split("_", 1)[1]
        all_services = list(SERVICES_CACHE.keys())
        service = _resolve_full_key(clean_service, all_services)
        countries = get_active_countries_for_service(service)
        if not countries:
            await query.edit_message_text("No countries currently available for this service.")
            return

        buttons = []
        show_country_count = get_setting("show_country_count", "false") == "true"
        for i in range(0, len(countries), 2):
            country_a = countries[i]
            label_a = f"{country_a} ({SERVICES_CACHE.get(service, {}).get(country_a, 0)})" if show_country_count else country_a
            row = [create_button(label_a, callback_data=f"cnt_{_cb_clean(service)}_{_cb_clean(country_a)}", style="primary")]
            if i + 1 < len(countries):
                country_b = countries[i + 1]
                label_b = f"{country_b} ({SERVICES_CACHE.get(service, {}).get(country_b, 0)})" if show_country_count else country_b
                row.append(create_button(label_b, callback_data=f"cnt_{_cb_clean(service)}_{_cb_clean(country_b)}", style="primary"))
            buttons.append(row)

        buttons.append([create_button("Back", callback_data="back_to_services", style="danger", icon_custom_emoji_id="5456187398977247949")])
        await query.edit_message_text(
            f'<tg-emoji emoji-id="5352922460897452503">📍</tg-emoji> Select country for {safe_html_escape(service)}:',
            reply_markup=InlineKeyboardMarkup(buttons), parse_mode="HTML"
    )

    elif data.startswith("cnt_"):
        parts = data.split("_", 2)
        if len(parts) < 3:
            await query.answer()
            await query.edit_message_text("Invalid command.")
            return
        service_clean, country_clean = parts[1], parts[2]
        all_services = list(SERVICES_CACHE.keys())
        service = _resolve_full_key(service_clean, all_services)
        if service in SERVICES_CACHE:
            country = _resolve_full_key(country_clean, list(SERVICES_CACHE[service].keys()))
        else:
            country = country_clean

        if is_country_paused_sync(service, country) or SERVICES_CACHE.get(service, {}).get(country, 0) <= 0:
            await query.answer("⏸️ This country is currently paused or out of stock.", show_alert=True)
            return

        await query.answer()

        if not user_is_admin:
            ok, wait_s = _check_number_cooldown(user_id)
            if not ok:
                await query.answer(
                    f"⏳ Please wait {wait_s}s before getting a new number.",
                    show_alert=True,
                )
                return
        if len(_LAST_NUMBER_CLAIM) >= _ANTI_ABUSE_STATE_MAX:
            _prune_ts_cache(_LAST_NUMBER_CLAIM, max(NUMBER_CLAIM_COOLDOWN * 4, 60.0), _ANTI_ABUSE_STATE_MAX - 1)
        _LAST_NUMBER_CLAIM[user_id] = time.monotonic()

        target_qty = int(get_setting("number_quantity", "2") or 2)
        assigned_numbers = await run_db(allocate_numbers_sync, service, country, user_id, target_qty)
        if not assigned_numbers:
            await query.edit_message_text(f"Sorry, not enough ({target_qty}) numbers available.")
            return

        context.user_data['last_allocated_numbers'] = assigned_numbers
        context.user_data['last_service'] = service
        context.user_data['last_country'] = country

        hide_cc = await run_db(get_user_hide_cc_sync, user_id)
        alloc_msg = f"━━━━━━━━━━━━━━━\n{safe_html_escape(service)} ➜ {safe_html_escape(country)}'s Numbers:"
        kbd = build_allocation_keyboard(service, country, assigned_numbers, hide_cc=hide_cc)
        await query.edit_message_text(alloc_msg, reply_markup=kbd, parse_mode="HTML")

    elif data.startswith("togcc:"):
        await query.answer()
        parts = data.split(":", 3)
        if len(parts) >= 4:
            service_clean = parts[1]
            country_clean = parts[2]
            hide_cc = (parts[3] == "1")
            all_services = list(SERVICES_CACHE.keys())
            service = _resolve_full_key(service_clean, all_services)
            if service in SERVICES_CACHE:
                country = _resolve_full_key(country_clean, list(SERVICES_CACHE[service].keys()))
            else:
                country = country_clean

            numbers = context.user_data.get('last_allocated_numbers')
            if not numbers or context.user_data.get('last_service') != service or context.user_data.get('last_country') != country:
                all_nums = await run_db(get_user_allocations_sync, user_id, service, country)
                target_qty = int(get_setting("number_quantity", "2") or 2)
                numbers = all_nums[-target_qty:] if all_nums else []
                context.user_data['last_allocated_numbers'] = numbers
                context.user_data['last_service'] = service
                context.user_data['last_country'] = country

            if not numbers:
                await query.answer("No numbers found!", show_alert=True)
                return

            await run_db(set_user_hide_cc_sync, user_id, hide_cc)

            alloc_msg = f"━━━━━━━━━━━━━━━\n{safe_html_escape(service)} ➜ {safe_html_escape(country)}'s Numbers:"
            kbd = build_allocation_keyboard(service, country, numbers, hide_cc=hide_cc)

            try:
                await query.edit_message_text(alloc_msg, reply_markup=kbd, parse_mode="HTML")
            except Exception:
                pass
            await query.answer("Country code hidden!" if hide_cc else "Country code shown!")

    elif data.startswith("chg:"):
        parts = data.split(":", 2)
        if len(parts) < 3:
            await query.answer("Invalid request!", show_alert=True)
            return
        service_clean, country_clean = parts[1], parts[2]
        all_services = list(SERVICES_CACHE.keys())
        service = _resolve_full_key(service_clean, all_services)
        if service in SERVICES_CACHE:
            country = _resolve_full_key(country_clean, list(SERVICES_CACHE[service].keys()))
        else:
            country = country_clean

        if is_country_paused_sync(service, country) or SERVICES_CACHE.get(service, {}).get(country, 0) <= 0:
            await query.answer("⏸️ This country is currently paused or out of stock.", show_alert=True)
            return

        if not user_is_admin:
            ok, wait_s = _check_number_cooldown(user_id)
            if not ok:
                await query.answer(
                    f"⏳ Please wait {wait_s}s before changing numbers.",
                    show_alert=True,
                )
                return

            should_ban, change_count = _record_change_and_check_ban(user_id)
            if should_ban:
                win_s = get_abuse_ban_window()
                await run_db(
                    set_user_banned_sync, user_id, True,
                    f"Auto-ban: {change_count} changes in {win_s}s",
                )
                _RECENT_NUMBER_CHANGES.pop(user_id, None)
                _LAST_NUMBER_CLAIM.pop(user_id, None)

                name = query.from_user.full_name or query.from_user.username or f"User {user_id}"
                await _notify_admins_ban(
                    context, user_id, name,
                    f"{change_count} number changes in {win_s}s",
                )
                await _send_banned_message(context.bot, user_id)
                await query.answer(
                    "🚫 You have been banned for number abuse.", show_alert=True,
                )
                return

        if len(_LAST_NUMBER_CLAIM) >= _ANTI_ABUSE_STATE_MAX:
            _prune_ts_cache(_LAST_NUMBER_CLAIM, max(NUMBER_CLAIM_COOLDOWN * 4, 60.0), _ANTI_ABUSE_STATE_MAX - 1)
        _LAST_NUMBER_CLAIM[user_id] = time.monotonic()

        target_qty = int(get_setting("number_quantity", "2") or 2)
        old_numbers = await run_db(get_user_allocations_sync, user_id, service, country)
        new_numbers = await run_db(allocate_numbers_sync, service, country, user_id, target_qty, old_numbers)
        if new_numbers:
            await query.answer("Numbers changed!", show_alert=False)

            context.user_data['last_allocated_numbers'] = new_numbers
            context.user_data['last_service'] = service
            context.user_data['last_country'] = country

            hide_cc = await run_db(get_user_hide_cc_sync, user_id)
            alloc_msg = f"━━━━━━━━━━━━━━━\n{safe_html_escape(service)} ➜ {safe_html_escape(country)}'s Numbers:"
            kbd = build_allocation_keyboard(service, country, new_numbers, hide_cc=hide_cc)
            await query.edit_message_text(alloc_msg, reply_markup=kbd, parse_mode="HTML")
        else:
            await query.answer(f"Not enough new numbers!", show_alert=True)


def _compute_msg_id(item: dict) -> Optional[str]:
    try:
        num = str(item.get("num", "")).strip()
        dt = item.get("dt", "")
        msg = item.get("message", "")
        if not num or not msg:
            return None
        return hashlib.md5(f"{num}_{dt}_{msg}".encode()).hexdigest()
    except Exception:
        return None


def _filter_new_items(items: list, processed_ids: TimedLRUDict) -> Tuple[list, list]:
    valid = []
    new_ids = []
    for item in items:
        if not isinstance(item, dict):
            continue
        pv = item.get("payout")
        if pv is not None:
            try:
                if float(pv) <= 0:
                    continue
            except (ValueError, TypeError):
                pass

        mid = _compute_msg_id(item)
        if not mid:
            continue
        if mid in processed_ids:
            continue
        processed_ids.add(mid)
        new_ids.append(mid)
        valid.append(item)
    return valid, new_ids


def _build_premium_otp_html(
    short_country: str,
    full_country: str,
    service: str,
    number: str,
    otp_code: str,
    full_message: str,
    channel_link: str,
    bot_link: str,
    show_dev: bool,
    dev_name: str,
    dev_link: str,
    show_msg: bool,
    cli_emoji: str = "",
) -> str:
    prefix_mask, number_mask = mask_number_premium(number)
    
    # 🆕 ইমোজি রিমুভ করা হলো
    clean_full_country = strip_all_emojis(full_country)

    # Premium Emoji IDs
    e_country = '<tg-emoji emoji-id="5375177250553487549">🏳️</tg-emoji>'
    e_number = '<tg-emoji emoji-id="5404435834789187002">📞</tg-emoji>'
    e_otp = '<tg-emoji emoji-id="5472239203590888751">💬</tg-emoji>'
    e_copy = '<tg-emoji emoji-id="5778137984276632041">🔑</tg-emoji>'
    e_channel = '<tg-emoji emoji-id="5296639349729800444">📢</tg-emoji>'
    e_bot = '<tg-emoji emoji-id="4940635119791637363">🤖</tg-emoji>'

    # Header (Table 1)
    header_content = f"<b>{safe_html_escape(short_country)}</b> {cli_emoji} <b>{safe_html_escape(service)}</b>"
    header_table = f"<table compact><tr><td align=\"center\">{header_content}</td></tr></table>"

    # Data (Table 2)
    data_table = (
        "<table bordered striped>"
        f"<tr><td>{e_country} COUNTRY</td><td><code>{html.escape(clean_full_country)}</code></td></tr>"
        f"<tr><td>{e_number} NUMBER</td><td><code>{html.escape(number_mask)}</code></td></tr>"
        f"<tr><td>{e_otp} OTP</td><td><code>{html.escape(otp_code)}</code></td></tr>"
        "</table>"
    )

    parts: List[str] = [header_table, data_table]

    # Message Button (Copies full message)
    if show_msg:
        label_text = full_message.replace("\n", " ").strip()
        btn_label = label_text[:60] + "..." if len(label_text) > 60 else label_text
        copy_text_esc = html.escape(full_message, quote=True)
        
        parts.append("<tg-button-row>")
        parts.append(
            f"<tg-button type=\"copy_text\" style=\"success\" "
            f"text=\"{copy_text_esc}\">"
            f"{e_copy} {html.escape(btn_label)}</tg-button>"
        )
        parts.append("</tg-button-row>")

    # Channel & Number Buttons
    parts.append("<tg-button-row>")
    parts.append(f"<tg-button type=\"url\" style=\"primary\" url=\"{html.escape(channel_link, quote=True)}\">{e_channel} CHANNEL</tg-button>")
    parts.append(f"<tg-button type=\"url\" style=\"primary\" url=\"{html.escape(bot_link, quote=True)}\">{e_bot} NUMBER</tg-button>")
    parts.append("</tg-button-row>")

    # Developer Button
    if show_dev and dev_name and dev_link:
        parts.append("<tg-button-row>")
        parts.append(
            f"<tg-button type=\"url\" style=\"primary\" url=\"{html.escape(dev_link, quote=True)}\">"
            f"🖥️ DEVELOPER: {html.escape(dev_name.upper())}</tg-button>"
        )
        parts.append("</tg-button-row>")

    return "".join(parts)


def _build_premium_dm_html(
    short_country: str,
    full_country: str,
    service: str,
    number: str,
    otp_code: str,
    full_message: str,
    payout_str: str,
    bal_str: str,
    show_msg: bool,
    cli_emoji: str = "",
) -> str:
    # 🆕 ইমোজি রিমুভ করা হলো
    clean_full_country = strip_all_emojis(full_country)

    # Premium Emoji IDs
    e_country = '<tg-emoji emoji-id="5375177250553487549">🏳️</tg-emoji>'
    e_number = '<tg-emoji emoji-id="5404435834789187002">📞</tg-emoji>'
    e_added = '<tg-emoji emoji-id="6206375377925839184">➕</tg-emoji>'
    e_balance = '<tg-emoji emoji-id="5417924076503062111">💳</tg-emoji>'
    e_copy = '<tg-emoji emoji-id="5778137984276632041">🔑</tg-emoji>'

    # Header: Service - Short Name
    header_content = f"<b>{safe_html_escape(short_country)}</b> {cli_emoji} <b>{safe_html_escape(service)}</b>"
    header_table = f"<table compact><tr><td align=\"center\">{header_content}</td></tr></table>"

    # Data Table (🆕 এখানে number_mask এর জায়গায় ফুল number বসানো হলো)
    data_table = (
        "<table bordered striped>"
        f"<tr><td>{e_country} COUNTRY</td><td><code>{html.escape(clean_full_country)}</code></td></tr>"
        f"<tr><td>{e_number} NUMBER</td><td><code>{html.escape(number)}</code></td></tr>"
        f"<tr><td>{e_added} ADDED</td><td><code>{payout_str} BDT</code></td></tr>"
        f"<tr><td>{e_balance} BALANCE</td><td><code>{bal_str} BDT</code></td></tr>"
        "</table>"
    )

    parts: List[str] = [header_table, data_table]

    # Copy Button (Label = Full Message, Copies = OTP Code)
    if show_msg:
        label_text = otp_code
        btn_label = label_text[:60] + "..." if len(label_text) > 60 else label_text
        copy_code_esc = html.escape(otp_code, quote=True)
        
        parts.append("<tg-button-row>")
        parts.append(
            f"<tg-button type=\"copy_text\" style=\"success\" "
            f"text=\"{copy_code_esc}\">"
            f"{e_copy} {html.escape(btn_label)}</tg-button>"
        )
        parts.append("</tg-button-row>")

    return "".join(parts)
    
def _build_regular_otp_html(
    short_country: str,
    service: str,
    number: str,
    otp_code: str,
    full_message: str,
    channel_link: str,
    bot_link: str,
    show_msg: bool,
    show_dev: bool,
    dev_name: str,
    dev_link: str,
    copy_keyboard,
) -> str:
    """Legacy regular text — returns HTML body; caller adds reply_markup."""
    safe_short = safe_html_escape(short_country)
    safe_service = safe_html_escape(service)
    safe_masked = html.escape(mask_number_aph(number))
    safe_msg = html.escape(full_message)

    if show_msg:
        body = (
            f"<b>{safe_short}</b> › <b>{safe_service}</b>\n\n"
            f"☎️ Number: {safe_masked}\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"🗨️ SMS:\n"
            f"<blockquote expandable>{safe_msg}</blockquote>\n"
            f"━━━━━━━━━━━━━━━━━\n"
        )
    else:
        body = (
            f"<b>{safe_short}</b> › {safe_service}\n\n"
            f"☎️ Number: {safe_masked}\n"
            f"━━━━━━━━━━━━━━━━━\n"
        )
    if show_dev:
        dev_html = f'<a href="{dev_link}">{html.escape(dev_name)}</a>'
        body += f"🖥️ Dᴇᴠᴇʟᴏᴘᴇʀ {dev_html}"
    return body


async def process_otp_items_fast(items: list, application: Application):
    if not items:
        return

    # ═══════════════════════════════════════════════════════════
    # ⚡ OPT 1: Start allocation lookup IMMEDIATELY (background task)
    # ═══════════════════════════════════════════════════════════
    numbers = [str(it.get("num", "")).strip() for it in items]
    clean_numbers = [re.sub(r'\D', '', n) for n in numbers]
    combined = list(set(numbers + clean_numbers))

    def _fetch_allocations_sync():
        result_map = {}
        try:
            for i in range(0, len(combined), 200):
                chunk = combined[i:i+200]
                rows = supabase.table("allocations").select(
                    "number, user_id, service, country"
                ).in_("number", chunk).execute().data or []
                for r in rows:
                    result_map[r["number"]] = r
        except Exception as e:
            logger.error(f"batch alloc lookup error: {e}")
        return result_map

    alloc_task = asyncio.create_task(run_db(_fetch_allocations_sync))

    # ═══════════════════════════════════════════════════════════
    # ⚡ OPT 2: Pre-load cached settings WHILE allocation runs
    # (These are nearly instant - cache hits)
    # ═══════════════════════════════════════════════════════════
    bot_username, bot_link = await _get_bot_info(application)

    ch_link = clean_tg_link(get_setting("channel", "https://t.me/your_channel"))
    show_msg_enabled = get_setting("show_message", "true") == "true"
    show_dev_enabled = get_setting("show_developer", "true") == "true"
    dev_username = get_setting("dev_username", "developer")
    dev_link = clean_tg_link(get_setting("dev_link", "https://t.me/developer"))
    target_otp_group = get_setting("otp_group_id", OTP_GROUP_ID)
    otp_format = get_setting("otp_group_format", "regular")
    premium_mode = (otp_format == "premium")

    # ═══════════════════════════════════════════════════════════
    # ⚡ OPT 3: Await allocation result
    # ═══════════════════════════════════════════════════════════
    alloc_map = await alloc_task

    # Group items by user
    per_user: Dict[int, dict] = {}
    service_country_pairs = set()
    for it in items:
        num = str(it.get("num", "")).strip()
        clean = re.sub(r'\D', '', num)
        alloc = alloc_map.get(num) or alloc_map.get(clean)
        if not alloc:
            continue
        service_country_pairs.add((alloc["service"], alloc["country"]))
        u = alloc["user_id"]
        if u not in per_user:
            per_user[u] = {"amount": 0.0, "count": 0, "items": []}
        per_user[u]["items"].append((it, alloc))
        per_user[u]["count"] += 1

    if not per_user:
        return

    # ═══════════════════════════════════════════════════════════
    # ⚡ OPT 4: Fetch missing payouts + user profiles IN PARALLEL
    # (single gather, runs concurrently)
    # ═══════════════════════════════════════════════════════════
    missing_pairs = [
        (s, c) for (s, c) in service_country_pairs
        if s not in PAYOUTS_CACHE or c not in PAYOUTS_CACHE.get(s, {})
    ]

    async def _fetch_profile(uid: int):
        try:
            prof = await run_db(get_user_profile_sync, uid)
            return (uid, prof)
        except Exception:
            return (uid, {"balance": 0.0, "total_otps": 0})

    identities_task = asyncio.create_task(run_db(get_user_identities_batch_sync, list(per_user.keys())))

    parallel_tasks = []
    if missing_pairs:
        parallel_tasks.extend([run_db(get_payout_sync, s, c) for (s, c) in missing_pairs])
    parallel_tasks.extend([_fetch_profile(uid) for uid in per_user.keys()])

    results = await asyncio.gather(*parallel_tasks, return_exceptions=True)
    try:
        identities_map = await identities_task
    except Exception:
        identities_map = {}

    old_profiles: Dict[int, dict] = {}
    offset = len(missing_pairs) if missing_pairs else 0
    for r in results[offset:]:
        if isinstance(r, tuple) and len(r) == 2 and isinstance(r[0], int):
            old_profiles[r[0]] = r[1]

    # ═══════════════════════════════════════════════════════════
    # ⚡ OPT 5: Calculate per-item payouts + optimistic balances
    # ═══════════════════════════════════════════════════════════
    item_payout_map: Dict[int, list] = {}
    for u, data in per_user.items():
        lst = []
        for it, alloc in data["items"]:
            p = float(get_payout_sync(alloc["service"], alloc["country"]))
            data["amount"] += p
            lst.append((it, alloc, p))
        item_payout_map[u] = lst

    # Local optimistic balances (real DB update happens in background below)
    display_profiles: Dict[int, dict] = {}
    for u, data in per_user.items():
        old = old_profiles.get(u) or {"balance": 0.0, "total_otps": 0}
        display_profiles[u] = {
            "balance": old["balance"] + data["amount"],
            "total_otps": old["total_otps"] + data["count"],
        }

    # ═══════════════════════════════════════════════════════════
    # ⚡ OPT 6: FIRE-AND-FORGET earnings DB update
    # (runs WHILE we're building and sending Telegram messages)
    # ═══════════════════════════════════════════════════════════
    batch_updates = [
        {"user_id": u, "amount": d["amount"], "count": d["count"]}
        for u, d in per_user.items()
    ]

    async def _bg_update_earnings():
        try:
            await run_db(add_otp_earnings_batch_sync, batch_updates)
        except Exception as e:
            logger.error(f"bg earnings update failed: {e}")

    asyncio.create_task(_bg_update_earnings())

    # ═══════════════════════════════════════════════════════════
    # ⚡ Build and send all messages IN PARALLEL
    # ═══════════════════════════════════════════════════════════
    send_tasks = []
    live_events_batch = []
    batch_ts = time.time()
    for u, data in per_user.items():
        prof = display_profiles.get(u) or {"balance": 0.0, "total_otps": 0}
        bal_str = fmt_num(prof["balance"])

        for item, alloc, item_payout in item_payout_map[u]:
            num = str(item.get("num", "")).strip()
            msg = item.get("message", "")
            cli = (item.get("cli") or "").strip()
            display_service = cli if cli else (alloc.get("service") or "Service")

            short_country = get_country_short_sync(alloc["service"], alloc["country"])
            full_country = alloc.get("country", "Unknown")

            otp_code = extract_otp(msg)

            # 📡 Collect Live Receiver Event for batched DB persistence
            u_ident = identities_map.get(u, {})
            live_events_batch.append({
                "user_id": int(u),
                "first_name": u_ident.get("first_name") or f"User {u}",
                "username": u_ident.get("username") or "",
                "service": display_service,
                "country": full_country,
                "number": num,
                "otp_code": otp_code,
                "payout": item_payout,
                "ts": batch_ts,
            })

            safe_msg = html.escape(msg)
            safe_service = safe_html_escape(display_service)
            safe_short = safe_html_escape(short_country)
            safe_num = html.escape(num)
            safe_masked_num = html.escape(mask_number_aph(num))
            payout_str = fmt_num(item_payout)

            # CLI Emoji Lookup
            clean_name = re.sub(r'<tg-emoji.*?>.*?</tg-emoji>', '', display_service)
            cli_clean = remove_emojis(clean_name).strip().lower()

            cli_emoji_id = get_setting(f"cli_emoji:{cli_clean}", "")
            cli_emoji_html = (
                f'<tg-emoji emoji-id="{cli_emoji_id}">🎲</tg-emoji>'
                if cli_emoji_id else ""
            )

            # ── OTP Group message ──
            if target_otp_group:
                if premium_mode:
                    premium_html = _build_premium_otp_html(
                        short_country=short_country,
                        full_country=full_country,
                        service=display_service,
                        number=num,
                        otp_code=otp_code,
                        full_message=msg,
                        channel_link=ch_link,
                        bot_link=bot_link,
                        show_dev=show_dev_enabled,
                        dev_name=dev_username,
                        dev_link=dev_link,
                        show_msg=show_msg_enabled,
                        cli_emoji=cli_emoji_html,
                    )
                    send_tasks.append(_safe_send_rich(application.bot, target_otp_group, premium_html))
                else:
                    group_text = _build_regular_otp_html(
                        short_country=short_country,
                        service=display_service,
                        number=num,
                        otp_code=otp_code,
                        full_message=msg,
                        channel_link=ch_link,
                        bot_link=bot_link,
                        show_msg=show_msg_enabled,
                        show_dev=show_dev_enabled,
                        dev_name=dev_username,
                        dev_link=dev_link,
                        copy_keyboard=None,
                    )
                    group_kbd = InlineKeyboardMarkup([
                        [create_button("Channel", url=ch_link, style="primary"),
                         create_button("Get Number", url=bot_link, style="primary")],
                        [create_button(f"{otp_code}", copy_text=otp_code, style="success")]
                    ])
                    send_tasks.append(_safe_send(
                        application.bot, target_otp_group,
                        text=group_text, reply_markup=group_kbd,
                        parse_mode="HTML",
                        link_preview_options=LinkPreviewOptions(is_disabled=True),
                    ))

            # ── User DM message ──
            if premium_mode:
                dm_html = _build_premium_dm_html(
                    short_country=short_country,
                    full_country=full_country,
                    service=display_service,
                    number=num,
                    otp_code=otp_code,
                    full_message=msg,
                    payout_str=payout_str,
                    bal_str=bal_str,
                    show_msg=show_msg_enabled,
                    cli_emoji=cli_emoji_html,
                )
                send_tasks.append(_safe_send_rich(application.bot, u, dm_html))
            else:
                if show_msg_enabled:
                    user_text = (
                        "— — — — — — — — — —\n"
                        f"<blockquote>📱 SERVICE: {safe_service}</blockquote>\n"
                        f"<blockquote>📞 NUMBER: {safe_num}</blockquote>\n"
                        f"<blockquote>➕ ADDED  ➜ {payout_str} BDT</blockquote>\n"
                        f"<blockquote>💳 BALANCE ➜ {bal_str} BDT</blockquote>\n"
                        "🗨️ MESSAGE: \n"
                        f"<blockquote expandable>{safe_msg}</blockquote>\n"
                        "— — — — — — — — — —"
                    )
                else:
                    user_text = (
                        "— — — — — — — — — —\n"
                        f"<blockquote>📱 SERVICE: {safe_service}</blockquote>\n"
                        f"<blockquote>📞 NUMBER: {safe_num}</blockquote>\n"
                        f"<blockquote>➕ ADDED  ➜ {payout_str} BDT</blockquote>\n"
                        f"<blockquote>💳 BALANCE ➜ {bal_str} BDT</blockquote>\n"
                        "— — — — — — — — — —"
                    )
                user_kbd = InlineKeyboardMarkup([
                    [create_button(f"{otp_code}", copy_text=otp_code, style="success")]
                ])
                send_tasks.append(_safe_send(
                    application.bot, u,
                    text=user_text, reply_markup=user_kbd, parse_mode="HTML",
                ))

    if live_events_batch:
        async def _bg_record_live_events(batch):
            try:
                await run_db(record_live_receiver_events_batch_sync, batch)
            except Exception as e:
                logger.error(f"bg record_live_receiver_events failed: {e}")
        asyncio.create_task(_bg_record_live_events(live_events_batch))

    if send_tasks:
        await asyncio.gather(*send_tasks, return_exceptions=True)

async def poll_single_panel(panel_id: str, application: Application,
                            processed_ids: TimedLRUDict):
    async with httpx.AsyncClient(
        timeout=httpx.Timeout(API_FETCH_TIMEOUT, connect=5.0),
        limits=httpx.Limits(max_connections=5, max_keepalive_connections=2),
        follow_redirects=True,
        headers={"User-Agent": "Mozilla/5.0 (compatible; OTPBot/1.0)"},
        verify=True,
    ) as client:
        error_streak = 0
        consecutive_log_skips = 0

        # 🚀 Helper: DB-তে seen mark করা ব্যাকগ্রাউন্ডে করি (ডেলিভারি ডিলে এড়াতে)
        async def _bg_mark_seen(mids: list):
            try:
                await run_db(mark_otp_seen_batch_sync, mids)
            except Exception as e:
                for mid in mids:
                    processed_ids.pop(mid, None)
                logger.error(f"bg mark_otp_seen failed, rolled back {len(mids)}: {e}")

        while True:
            panel = await run_db(_get_panel_cached_sync, panel_id)
            if not panel:
                await asyncio.sleep(5)
                continue

            url = panel["url"]
            token = panel["token"]
            interval = float(panel.get("polling_interval", 5.0))
            if interval < 3.1:
                interval = 3.1
            elif interval > 120.0:
                interval = 120.0

            if get_panel_type(panel) == "captcha":
                try:
                    cfg = json.loads(panel.get("mapping_json") or "{}")
                except Exception:
                    cfg = {}

                sess = CAPTCHA_SESSIONS.get(panel_id)
                if not sess:
                    ok, status = await attempt_captcha_login(panel_id, panel, cfg)
                    CAPTCHA_PANEL_STATUS[panel_id] = status
                    if not ok:
                        logger.info(f"Captcha panel {panel_id}: {status}")
                        await asyncio.sleep(30)
                        continue

                items, status = await fetch_captcha_panel_data(panel_id, cfg)
                CAPTCHA_PANEL_STATUS[panel_id] = status

                status_lower = status.lower()
                if ("expired" in status_lower
                        or "error" in status_lower
                        or "not json" in status_lower
                        or "empty response" in status_lower):
                    old = CAPTCHA_SESSIONS.pop(panel_id, None)
                    if old:
                        try:
                            await old["client"].aclose()
                        except Exception:
                            pass
                    logger.info(f"Captcha panel {panel_id}: {status} — forcing re-login")
                    await asyncio.sleep(3)
                    continue

                if items:
                    new_items, new_ids = _filter_new_items(items, processed_ids)
                    if new_items:
                        logger.info(f"Captcha Panel {panel_id}: {len(new_items)} new items → delivering")
                        # ⚡ Fire-and-forget: DB mark ব্যাকগ্রাউন্ডে
                        asyncio.create_task(_bg_mark_seen(new_ids))

                        async def _safe_process_cpt(it, app):
                            try:
                                await process_otp_items_fast(it, app)
                            except Exception as e:
                                logger.exception(f"process_otp_items_fast CRASHED: {e}")
                        asyncio.create_task(_safe_process_cpt(new_items, application))

                await asyncio.sleep(interval)
                continue

            # ==========================================
            # 👇 AUGESTEL PANEL LOGIC
            # ==========================================
            if get_panel_type(panel) == "augestel":
                try:
                    cfg = json.loads(panel.get("mapping_json") or "{}")
                except Exception:
                    cfg = {}
                sess = AUGESTEL_SESSIONS.get(panel_id)
                if not sess:
                    ok, status = await _augestel_login(panel_id, panel, cfg)
                    AUGESTEL_PANEL_STATUS[panel_id] = status
                    if not ok:
                        logger.info(f"Augestel panel {panel_id}: {status}")
                        await asyncio.sleep(30)
                        continue

                items, status = await fetch_augestel_panel_data(panel_id, cfg)
                AUGESTEL_PANEL_STATUS[panel_id] = status
                status_lower = status.lower()
                if ("expired" in status_lower
                        or "error" in status_lower
                        or "not json" in status_lower
                        or "empty response" in status_lower):
                    await _augestel_close_session(panel_id)
                    logger.info(f"Augestel panel {panel_id}: {status} - forcing re-login")
                    await asyncio.sleep(3)
                    continue

                if items:
                    new_items, new_ids = _filter_new_items(items, processed_ids)
                    if new_items:
                        sources = ", ".join(set(i.get("source", "Unknown") for i in new_items))
                        logger.info(f"Augestel Panel {panel_id}: {len(new_items)} new items - delivering (Source: {sources})")
                        # ⚡ Fire-and-forget: DB mark ব্যাকগ্রাউন্ডে
                        asyncio.create_task(_bg_mark_seen(new_ids))

                        async def _safe_process_aug(it, app):
                            try:
                                await process_otp_items_fast(it, app)
                            except Exception as e:
                                logger.exception(f"process_otp_items_fast CRASHED: {e}")
                        asyncio.create_task(_safe_process_aug(new_items, application))

                # 👇 WebSocket ইভেন্টের জন্য অপেক্ষা
                ws_ev = sess.get("state", {}).get("ws_event")
                if ws_ev:
                    try:
                        await asyncio.wait_for(ws_ev.wait(), timeout=interval)
                    except asyncio.TimeoutError:
                        pass
                    finally:
                        ws_ev.clear()
                else:
                    await asyncio.sleep(interval)
                continue
            # ==========================================
            # 👆 AUGESTEL PANEL LOGIC ENDS
            # ==========================================

            mapping = None
            mapping_json = panel.get("mapping_json") or ""
            if mapping_json:
                try:
                    mapping = json.loads(mapping_json)
                except Exception as e:
                    logger.error(f"Panel {panel_id}: mapping_json parse error: {e}")
                    mapping = None

            try:
                if mapping:
                    custom_headers = {"Accept": "application/json"}
                    if token:
                        custom_headers["Authorization"] = f"Bearer {token}"
                    res = await client.get(url, headers=custom_headers)
                else:
                    params = {"records": API_RECORDS_PER_POLL}
                    if token and "token=" not in url:
                        params["token"] = token
                    res = await client.get(url, params=params)

                if res.status_code == 200:
                    try:
                        res_data = res.json()
                    except Exception as e:
                        logger.error(f"Panel {panel_id}: JSON parse error: {e}; body[:200]={res.text[:200]!r}")
                        res_data = {}

                    raw_items = []
                    if mapping:
                        raw_items = apply_custom_mapping(res_data, mapping)
                        if not raw_items and consecutive_log_skips < 3:
                            logger.info(
                                f"Panel {panel_id}: custom mapping returned 0 items; "
                                f"resp_keys={list(res_data.keys()) if isinstance(res_data, dict) else type(res_data).__name__}"
                            )
                            consecutive_log_skips += 1
                    else:
                        if isinstance(res_data, dict) and res_data.get("status") == "success":
                            raw_items = res_data.get("data", []) or []

                    if isinstance(raw_items, list) and raw_items:
                        new_items, new_ids = _filter_new_items(raw_items, processed_ids)
                        if new_items:
                            logger.info(f"Panel {panel_id}: {len(new_items)} new items → delivering")
                            # ⚡ Fire-and-forget: DB mark ব্যাকগ্রাউন্ডে
                            asyncio.create_task(_bg_mark_seen(new_ids))

                            async def _safe_process(items, app):
                                try:
                                    await process_otp_items_fast(items, app)
                                except Exception as e:
                                    logger.exception(f"process_otp_items_fast CRASHED: {e}")
                            asyncio.create_task(_safe_process(new_items, application))
                    error_streak = 0
                else:
                    error_streak += 1
                    if error_streak <= 3:
                        logger.warning(
                            f"Panel {panel_id}: HTTP {res.status_code} from {url[:120]}...; "
                            f"body[:200]={res.text[:200]!r}"
                        )
            except httpx.TimeoutException as e:
                error_streak += 1
                if error_streak <= 3:
                    logger.warning(f"Panel {panel_id}: TIMEOUT after {API_FETCH_TIMEOUT}s — {e}")
            except httpx.ConnectError as e:
                error_streak += 1
                if error_streak <= 3:
                    logger.warning(f"Panel {panel_id}: CONNECT ERROR — {e}")
            except Exception as e:
                error_streak += 1
                logger.exception(f"Panel {panel_id}: polling exception — {e}")

            sleep_t = interval * min(8, 2 ** min(error_streak, 3)) if error_streak else interval
            await asyncio.sleep(sleep_t)
            
async def otp_poller_manager(application: Application):
    loaded = await run_db(load_seen_otp_ids_sync) or {}
    processed_ids = TimedLRUDict(maxsize=PROCESSED_IDS_MAX, ttl=OTP_ID_RETENTION_SECONDS)
    for mid, ts in sorted(loaded.items(), key=lambda kv: float(kv[1] or 0)):
        try:
            processed_ids.add(mid, ts=float(ts) if ts else None)
        except Exception:
            processed_ids.add(mid)
    loaded.clear()
    await run_db(cleanup_old_live_receiver_events_sync)
    logger.info(f"OTP Poller Manager started. Loaded {len(processed_ids)} seen OTP ids.")

    cycle_count = 0
    last_reset_check = 0.0
    last_inact_sweep = 0.0

    while True:
        try:
            panels = await run_db(get_all_api_panels_sync)
            active_ids = {str(p["id"]) for p in panels}

            for pid in list(PANEL_TASKS.keys()):
                if pid not in active_ids or PANEL_TASKS[pid].done():
                    if not PANEL_TASKS[pid].done():
                        PANEL_TASKS[pid].cancel()
                    del PANEL_TASKS[pid]

            for p in panels:
                pid = str(p["id"])
                if pid not in PANEL_TASKS or PANEL_TASKS[pid].done():
                    PANEL_TASKS[pid] = asyncio.create_task(
                        poll_single_panel(pid, application, processed_ids)
                    )
                    logger.info(f"Started poller task for panel {pid} ({p.get('name')})")

            cycle_count += 1
            if cycle_count % CLEANUP_EVERY_N_CYCLES == 0:
                await run_db(cleanup_old_otp_ids_sync)
                await run_db(cleanup_old_live_receiver_events_sync)
                try:
                    processed_ids.prune()
                    AUGESTEL_PROCESSED_OTPS.prune()
                    prune_runtime_caches()
                    gc.collect()
                except Exception as e:
                    logger.error(f"prune error: {e}")

            now = time.time()
            if now - last_inact_sweep >= 3600:
                last_inact_sweep = now
                if is_inactive_autoban_enabled():
                    banned_inact = await run_db(run_inactive_autoban_sweep_sync)
                    for b in banned_inact:
                        await _send_banned_message(application.bot, b["uid"])

            if now - last_reset_check >= WEEKLY_RESET_CHECK_INTERVAL:
                last_reset_check = now
                notifications = await run_db(check_and_process_weekly_reset_sync)
                for n in notifications:
                    try:
                        msg = (
                            "🎉 <b>CONGRATULATIONS! WEEKLY RANKING BONUS!</b>\n\n"
                            f"You earned <b>{fmt_num(n['amount'])} ৳</b> for ranking <b>Top {n['rank']}</b>! 🏆"
                        )
                        await application.bot.send_message(chat_id=n["uid"], text=msg, parse_mode="HTML")
                    except Exception as e:
                        logging.error(f"rank notif err: {e}")

        except Exception as e:
            logging.error(f"OTP Poller Manager Error: {e}")

        await asyncio.sleep(5)


def main():
    if not init_supabase():
        logger.error("Failed to initialize Supabase. Exiting.")
        return

    init_firebase()
    refresh_all_caches_sync()

    if not SETTINGS_CACHE:
        restore_from_firebase_to_supabase()
        refresh_all_caches_sync()

    load_known_users()

    threading.Thread(target=run_flask, daemon=True).start()
    logger.info(f"Flask started on port {os.environ.get('PORT', 8080)}")

    application = (
        Application.builder()
        .token(TOKEN)
        .concurrent_updates(16)
        .build()
    )

    admin_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(admin_add_service_start, pattern="^adm:srv:add$"),
            CallbackQueryHandler(admin_add_service_with_name, pattern="^adm:srv:add:"),
            CallbackQueryHandler(admin_edit_service_start, pattern="^adm:srv:edit:"),
            CallbackQueryHandler(admin_country_add_numbers_start, pattern="^adm:c:an:"),
            CallbackQueryHandler(admin_edit_country_name_start, pattern="^adm:c:en:"),
            CallbackQueryHandler(admin_country_edit_payout_start, pattern="^adm:c:ep:"),
            CallbackQueryHandler(admin_add_panel_start, pattern="^adm:api:add$"),
            CallbackQueryHandler(admin_add_custom_panel_start, pattern="^adm:api:add_custom$"),
            CallbackQueryHandler(admin_add_captcha_panel_start, pattern="^adm:api:add_captcha$"),
            CallbackQueryHandler(admin_add_augestel_panel_start, pattern="^adm:api:add_augestel$"),
            CallbackQueryHandler(admin_add_admin_start, pattern="^adm:add:start$"),
            CallbackQueryHandler(set_channel_start, pattern="^adm:set:channel$"),
            CallbackQueryHandler(set_support_start, pattern="^adm:set:support$"),
            CallbackQueryHandler(set_otplink_start, pattern="^adm:set:otplink$"),
            CallbackQueryHandler(set_otpgroupid_start, pattern="^adm:set:otpgroupid$"),
            CallbackQueryHandler(set_dev_name_start, pattern="^adm:set:devname$"),
            CallbackQueryHandler(set_dev_link_start, pattern="^adm:set:devlink$"),
            CallbackQueryHandler(user_start_withdraw_flow, pattern="^usr:w_method:"),
            CallbackQueryHandler(admin_add_w_method_start, pattern="^adm:w_add_m$"),
            CallbackQueryHandler(admin_set_min_w_start, pattern="^adm:w_set_min$"),
            CallbackQueryHandler(admin_reject_w_start, pattern="^adm:w_rej_start:"),
            CallbackQueryHandler(set_rank1_bonus_start, pattern="^adm:r_set_b1$"),
            CallbackQueryHandler(set_rank2_bonus_start, pattern="^adm:r_set_b2$"),
            CallbackQueryHandler(set_rank3_bonus_start, pattern="^adm:r_set_b3$"),
            CallbackQueryHandler(start_edit_payout, pattern="^adm:pay:edit:"),
            CallbackQueryHandler(admin_fj_add_start, pattern="^adm:fj_add$"),
            CallbackQueryHandler(admin_set_refer_pct_start, pattern="^adm:refer_set_pct$"),
            CallbackQueryHandler(admin_search_user_start, pattern="^adm:usr:search$"),
            CallbackQueryHandler(admin_autoban_thresh_start, pattern="^adm:usr:ab:set_thresh$"),
            CallbackQueryHandler(admin_autoban_window_start, pattern="^adm:usr:ab:set_win$"),
            CallbackQueryHandler(admin_autoban_days_start, pattern="^adm:usr:ab:set_days$"),
            CallbackQueryHandler(admin_autoban_otps_start, pattern="^adm:usr:ab:set_otps$"),
            CallbackQueryHandler(admin_cliemoji_add_start, pattern="^adm:cliemoji:add$"),  # 🆕
            MessageHandler(filters.Regex(r"(?i)^(?:[\s\U0001F000-\U0010FFFF\u2600-\u27BF\u25A0-\u25FF\uFE0F\u200D]*)Broadcast$"), broadcast_start),
        ],
        states={
            ADD_SERVICE: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_service_name)],
            ADD_COUNTRY: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_country_name)],
            WAIT_COUNTRY_SHORT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_country_short)],
            WAIT_PAYOUT_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_payout_amount)],
            WAIT_CC_LENGTH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cc_length)],
            ADD_NUMBERS: [MessageHandler((filters.TEXT | filters.Document.ALL) & ~filters.COMMAND & ~MENU_FILTER, receive_numbers)],
            WAIT_PANEL_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_panel_name)],
            WAIT_PANEL_URL: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_panel_url)],
            WAIT_PANEL_TOKEN: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_panel_token)],
            WAIT_PANEL_INTERVAL: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_panel_interval)],
            WAIT_MAP_STATUS_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_status_path)],
            WAIT_MAP_STATUS_VALUE: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_status_value)],
            WAIT_MAP_DATA_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_data_path)],
            WAIT_MAP_NUM_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_num_path)],
            WAIT_MAP_MSG_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_msg_path)],
            WAIT_MAP_DT_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_dt_path)],
            WAIT_MAP_PAYOUT_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_payout_path)],
            WAIT_MAP_CLI_PATH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_map_cli_path)],
            WAIT_CPT_LOGIN_URL: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_login_url)],
            WAIT_CPT_USERNAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_username)],
            WAIT_CPT_PASSWORD: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_password)],
            WAIT_CPT_MSG_LINK: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_msg_link)],
            WAIT_CPT_NUM_COL_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_num_col_name)],
            WAIT_CPT_NUM_COL_IDX: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_num_col_idx)],
            WAIT_CPT_MSG_COL_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_msg_col_name)],
            WAIT_CPT_MSG_COL_IDX: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_msg_col_idx)],
            WAIT_CPT_DT_COL_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_dt_col_name)],
            WAIT_CPT_DT_COL_IDX: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cpt_dt_col_idx)],
            WAIT_ADMIN_ID: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_admin_id)],
            WAIT_ADMIN_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_admin_name)],
            WAIT_CHANNEL: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_channel_link)],
            WAIT_SUPPORT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_support_link)],
            WAIT_OTP_LINK: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_otp_link)],
            WAIT_OTP_GROUP_ID: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_otp_group_id)],
            WAIT_BROADCAST_MSG: [MessageHandler(~filters.COMMAND & ~MENU_FILTER, receive_broadcast_msg)],
            WAIT_WITHDRAW_WALLET: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_withdraw_wallet)],
            WAIT_WITHDRAW_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_withdraw_amount)],
            WAIT_NEW_WITHDRAW_METHOD: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_new_withdraw_method)],
            WAIT_MIN_WITHDRAW_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_min_withdraw_amount)],
            WAIT_REJECT_REASON: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_reject_reason)],
            WAIT_DEV_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_dev_name)],
            WAIT_DEV_LINK: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_dev_link)],
            WAIT_RANK1_BONUS: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_rank1_bonus)],
            WAIT_RANK2_BONUS: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_rank2_bonus)],
            WAIT_RANK3_BONUS: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_rank3_bonus)],
            WAIT_FJ_CHAT_ID: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_fj_chat_id)],
            WAIT_FJ_CHAT_TITLE: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_fj_chat_title)],
            WAIT_FJ_CHAT_LINK: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_fj_chat_link)],
            WAIT_FJ_CHAT_TYPE: [CallbackQueryHandler(handle_fj_chat_type, pattern="^adm:fj_type:")],
            WAIT_REFER_PERCENT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_refer_pct)],
            WAIT_USER_SEARCH: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_user_search)],
            WAIT_AUTOBAN_THRESHOLD: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_autoban_thresh)],
            WAIT_AUTOBAN_WINDOW: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_autoban_window)],
            WAIT_AUTOBAN_INACTIVE_DAYS: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_autoban_days)],
            WAIT_AUTOBAN_INACTIVE_OTPS: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_autoban_otps)],
            # 🆕 CLI Emoji States
            WAIT_CLI_EMOJI_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_cli_emoji_name)],
            WAIT_AUG_EMAIL: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_aug_email)],
            WAIT_AUG_PASSWORD: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_aug_password)],
            WAIT_AUG_API_KEY: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_aug_api_key)],
            WAIT_CLI_EMOJI_VAL: [MessageHandler(~filters.COMMAND & ~MENU_FILTER, receive_cli_emoji_val)],
            WAIT_EDIT_SERVICE_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_edit_service_name)],
            WAIT_EDIT_COUNTRY_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_edit_country_name)],
            WAIT_EDIT_COUNTRY_SHORT: [MessageHandler(filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, receive_edit_country_short)],
        },
        fallbacks=[
            CommandHandler("cancel", cancel),
            MessageHandler(MENU_FILTER, cancel)
        ],
        per_message=False,
        allow_reentry=True
    )

    application.add_handler(CommandHandler("start", start))
    application.add_handler(admin_conv)
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_menu))
    application.add_handler(CallbackQueryHandler(handle_callback))

    async def post_init(app: Application):
        try:
            await _get_bot_info(app, ttl=0.0)
        except Exception:
            pass

        t1 = asyncio.create_task(otp_poller_manager(app))
        t2 = asyncio.create_task(firebase_backup_worker())
        _BACKGROUND_TASKS.add(t1)
        _BACKGROUND_TASKS.add(t2)

        def _task_done(name):
            def _cb(t):
                _BACKGROUND_TASKS.discard(t)
                if t.cancelled():
                    logger.warning(f"{name} cancelled")
                else:
                    exc = t.exception()
                    if exc:
                        logger.error(f"{name} exited with exception: {exc}")
            return _cb

        t1.add_done_callback(_task_done("otp_poller_manager"))
        t2.add_done_callback(_task_done("firebase_backup_worker"))
        logger.info("Bot started: Supabase primary + Firebase backup")

    async def post_shutdown(app: Application):
        for pid, sess in list(CAPTCHA_SESSIONS.items()):
            try:
                await sess["client"].aclose()
            except Exception:
                pass
        CAPTCHA_SESSIONS.clear()
        for pid in list(AUGESTEL_SESSIONS.keys()):
            try:
                await _augestel_close_session(pid)
            except Exception:
                pass
        AUGESTEL_SESSIONS.clear()
        try:
            await asyncio.to_thread(push_dirty_to_firebase_sync)
            logger.info("Final Firebase backup complete")
        except Exception as e:
            logger.error(f"Shutdown backup error: {e}")

    application.post_init = post_init
    application.post_shutdown = post_shutdown
    application.run_polling()


if __name__ == "__main__":
    main()
