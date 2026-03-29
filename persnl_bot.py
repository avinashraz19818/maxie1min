import asyncio
import logging
import json
from pymongo import MongoClient
import aiohttp
import os
import random
import re
from datetime import datetime, timedelta
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, InputMediaVideo, InputMediaDocument
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes, MessageHandler, filters
from telegram.constants import ParseMode
from telegram.error import NetworkError, TimedOut, RetryAfter
import pandas as pd
from io import BytesIO
from PIL import Image, ImageDraw, ImageFont
import time
import base64
from collections import Counter, deque
import numpy as np
import pickle
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
import hashlib

# Pyrogram for user account (premium emoji support)
from pyrogram import Client
from pyrogram.errors import FloodWait, PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant
from pyrogram.enums import ParseMode as PyrogramParseMode
from pyrogram.types import InputMediaPhoto as PyrogramInputMediaPhoto
from pyrogram.types import InputMediaVideo as PyrogramInputMediaVideo
from pyrogram.types import InputMediaDocument as PyrogramInputMediaDocument

MONGO_URI = "mongodb+srv://avinash:avinash12@cluster0.wnwd1fv.mongodb.net/?appName=Cluster0"
MONGO_DB_NAME = "maxie1min"

# Configure logging
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)

class WinGoBotEnhanced:
    def __init__(self, bot_token, api_id=None, api_hash=None, phone=None):
        self.bot_token = bot_token
        self.config_file = 'wingo_config.json'
        self.templates_file = 'templates.json'
        self.emoji_config_file = 'emoji_config.json'
        self.mongo_client = MongoClient(MONGO_URI, serverSelectionTimeoutMS=5000)
        self.mongo = self.mongo_client[MONGO_DB_NAME]
        self.ai_model_file = 'ai_pattern_model.pkl'  # NEW: AI model file
        self.pattern_history_file = 'pattern_history.json'  # NEW: Pattern history

        # User account variables
        self.api_id = api_id
        self.api_hash = api_hash
        self.phone = phone
        self.user_app = None
        self.use_user_account = bool(api_id and api_hash and phone)
        self.resolved_peers = {}
        self.failed_peers = set()

        # Store emoji placeholders for auto-detection
        self.emoji_placeholders = {}

        # Session tracking - FIXED
        self.current_session = ""
        self.last_session_check = None
        self.session_ended = True
        self.waiting_for_win = False
        self.last_prediction_was_loss = False
        self.in_break_period = False
        self.night_mode = False
        self.morning_message_sent = False
        self.night_message_sent = False
        self.operational_hours_start = 6
        self.operational_hours_end = 23

        # Channel management
        self.active_channels = []
        self.channel_configs = {}
        self.channel_prediction_status = {}  # Track prediction status per channel

        # Track last sent message
        self.last_sent_period = None
        self.last_prediction_time = None

        # Single prediction mode
        self.current_prediction_period = None
        self.current_prediction_choice = None
        self.waiting_for_result = False
        self.break_message_sent = False
        self.last_result_was_win = False

        # Prediction tracking
        self.last_processed_period = None
        self.predictions = {}
        self.user_state = {}
        self.session_predictions = []

        # Advanced prediction tracking
        self.consecutive_losses = 0
        self.consecutive_wins = 0
        self.prediction_history = []
        self.last_10_results = []
        self.pattern_memory = deque(maxlen=1000)  # Increased for AI learning
        self.number_memory = deque(maxlen=1000)   # Increased for AI learning
        self.recent_results = deque(maxlen=200)   # Store recent results for AI
        self.recent_numbers = deque(maxlen=200)   # Store recent numbers for AI

        # Advanced loss prevention
        self.session_wins = 0
        self.session_losses = 0
        self.total_wins = 0
        self.total_losses = 0
        self.safety_mode = False
        self.recovery_mode = False
        self.ultra_safe_mode = False
        self.last_5_predictions = []

        # REAL AI PATTERN RECOGNITION SYSTEM - NEW
        self.ai_model = None
        self.scaler = None
        self.pattern_history = []
        self.successful_patterns = []
        self.failed_patterns = []
        self.learning_rate = 0.1
        self.pattern_database = {}
        self.ai_confidence_threshold = 0.75
        self.min_training_samples = 100
        
        # AI Learning Parameters
        self.pattern_window_size = 20  # Look at last 20 results for patterns
        self.feature_count = 15  # Number of features for AI
        self.ai_prediction_history = deque(maxlen=200)
        
        # Advanced pattern weights with AI adjustment
        self.pattern_weights = {
            'streak_breaker': 0.25,
            'balance_correction': 0.35,
            'gap_filling': 0.25,
            'number_pattern': 0.10,
            'alternating': 0.05,
            'random_walk': 0.15,
            'history_trend': 0.20,
            'ai_pattern': 0.45  # NEW: AI gets highest weight
        }

        # AI Pattern Learning
        self.learning_history = deque(maxlen=1000)
        self.last_winning_strategy = None
        self.strategy_success_count = {}
        self.recent_patterns = deque(maxlen=100)
        
        # Pattern detection variables
        self.big_small_history = deque(maxlen=500)  # Increased for AI
        self.number_distribution = {i: 0 for i in range(10)}
        self.prediction_streak_threshold = 3
        self.last_actual_results = deque(maxlen=100)  # Increased for AI
        
        # NEW: AI Statistics
        self.ai_correct_predictions = 0
        self.ai_total_predictions = 0
        self.ai_accuracy = 0.0
        self.ai_learning_cycles = 0
        self.last_ai_pattern_used = None
        
        # NEW: Advanced Pattern Types
        self.pattern_types = {
            'alternating': 0,
            'streak': 0,
            'zigzag': 0,
            'cluster': 0,
            'random': 0,
            'cycle': 0
        }

        # Default templates with ACTUAL EMOJIS
        self.default_templates = {
            "prediction_header": "{crown} 𝐁𝐃𝐆 𝐖𝐈𝐍 𝐖𝐈𝐍𝐆𝐎 𝐎𝐅𝐅𝐈𝐂𝐈𝐀𝐋 {crown}\n   ——————————————\n        {sparkles} 𝟭 𝗠𝗜𝗡  𝗪𝗜𝐍𝐆𝐎  {sparkles}\n    —————————————",
            "session_line": "      {check} 𝐒𝐄𝐒𝐒𝐈𝐎𝐍: {session}",
            "maintain_level": "    —————————————\n    {chart}  MAINTAIN 8 LEVEL  {chart}\n    —————————————",
            "prediction_footer": "\n\n\n\n\n\n    {link} 𝐑𝐞𝐠𝐢𝐬𝐭𝐞𝐫 𝐋𝐢𝐧𝐤: \n    {register_link}\n    \n    —————————————\n    \n    {promo_text}\n    \n    —————————————",
            "good_morning": "{sun} 𝐆𝐎𝐎𝐃 𝐌𝐎𝐑𝐍𝐈𝐍𝐆 𝐖𝐈𝐍𝐍𝐄𝐑𝐒! {sun}\n\n{sparkles} A new day of winning begins!\n{lightning} Starting at 6:00 AM sharp!\n{money} Let's make today profitable!\n\n{coffee} Have your coffee ready...\n{rocket} Ultra-smart predictions starting soon!",
            "good_night": "{moon} 𝐆𝐎𝐎𝐃 𝐍𝐈𝐆𝐇𝐓 𝐖𝐈𝐍𝐍𝐄𝐑𝐒! {moon}\n\n{sleep} Going to sleep now...\n{clock} Will be back tomorrow at 6:00 AM\n\n{moon} Sweet dreams winners!\n{reload} See you tomorrow for more wins!",
            "break_message": "{break_icon} 𝐁𝐑𝐄𝐀𝐊 𝐓𝐈𝐌𝐄 {break_icon}\n\n🌀 15 Minutes Break\n{clock} Next Session: {next_session}\n\n{sleep} Taking a short break...\n{reload} Back with even smarter predictions!\n\nDon't miss this opportunity!\n{target} Next session starts in 15 minutes...",
            "new_session": "{reload} 𝐍𝐄𝐖 𝐒𝐄𝐒𝐒𝐈𝐎𝐍 𝐒𝐓𝐀𝐑𝐓𝐄𝐃 {reload}\n\n{crown} 𝐁𝐃𝐆 𝐖𝐈𝐍 𝐖𝐈𝐍𝐆𝐎 𝐎𝐅𝐅𝐈𝐂𝐈𝐀𝐋 {crown}\n   ——————————————\n        {sparkles} 𝟭 𝗠𝗜𝗡  𝗪𝗜𝐍𝐆𝐎  {sparkles}\n    —————————————\n      {check} 𝐒𝐄𝐒𝐒𝐈𝐎𝐍: {session}\n    —————————————\n\n    —————————————\n\n    {rocket} Session Started! Ultra-accurate predictions incoming..."
        }

        # Custom break messages storage
        self.custom_break_messages = {}
        self.custom_break_schedules = {}
        self.media_group_messages = {}
        self.scheduled_tasks = {}
        
        # Track which custom messages have been sent in current break
        self.sent_custom_messages_in_break = {}
        
        # Initialize configurations
        self.initialize_configs()
        
        # NEW: Initialize AI Model
        self.initialize_ai_model()

    def initialize_ai_model(self):
        """Initialize AI Pattern Recognition Model"""
        try:
            if os.path.exists(self.ai_model_file):
                with open(self.ai_model_file, 'rb') as f:
                    saved_data = pickle.load(f)
                    self.ai_model = saved_data.get('model')
                    self.scaler = saved_data.get('scaler')
                    self.pattern_database = saved_data.get('pattern_database', {})
                    self.ai_accuracy = saved_data.get('ai_accuracy', 0.0)
                    self.ai_correct_predictions = saved_data.get('ai_correct_predictions', 0)
                    self.ai_total_predictions = saved_data.get('ai_total_predictions', 0)
                logging.info(f"✅ AI Model loaded: Accuracy = {self.ai_accuracy:.2%}")
            else:
                self.ai_model = RandomForestClassifier(
                    n_estimators=100,
                    max_depth=10,
                    random_state=42,
                    n_jobs=-1
                )
                self.scaler = StandardScaler()
                self.pattern_database = {}
                logging.info("✅ New AI Model created")
                
            # Load pattern history
            if os.path.exists(self.pattern_history_file):
                with open(self.pattern_history_file, 'r', encoding='utf-8') as f:
                    self.pattern_history = json.load(f)
                logging.info(f"✅ Pattern history loaded: {len(self.pattern_history)} patterns")
                
        except Exception as e:
            logging.error(f"❌ Error initializing AI model: {e}")
            self.ai_model = RandomForestClassifier(
                n_estimators=100,
                max_depth=10,
                random_state=42,
                n_jobs=-1
            )
            self.scaler = StandardScaler()
            self.pattern_database = {}

    def save_ai_model(self):
        """Save AI Model and pattern database"""
        try:
            saved_data = {
                'model': self.ai_model,
                'scaler': self.scaler,
                'pattern_database': self.pattern_database,
                'ai_accuracy': self.ai_accuracy,
                'ai_correct_predictions': self.ai_correct_predictions,
                'ai_total_predictions': self.ai_total_predictions
            }
            with open(self.ai_model_file, 'wb') as f:
                pickle.dump(saved_data, f)
            
            # Save pattern history
            with open(self.pattern_history_file, 'w', encoding='utf-8') as f:
                json.dump(self.pattern_history, f, indent=2, ensure_ascii=False)
                
            logging.info(f"✅ AI Model saved: Accuracy = {self.ai_accuracy:.2%}")
        except Exception as e:
            logging.error(f"❌ Error saving AI model: {e}")

    def extract_features_for_ai(self, results, numbers):
        """Extract advanced features for AI pattern recognition"""
        features = []
        
        if len(results) < self.pattern_window_size:
            # Return default features if not enough data
            return [0] * self.feature_count
        
        # Convert results to numerical (BIG=1, SMALL=0)
        result_numeric = [1 if r == 'BIG' else 0 for r in results]
        recent_results = result_numeric[:self.pattern_window_size]
        recent_numbers = numbers[:self.pattern_window_size]
        
        # 1. Streak features
        current_streak = 1
        for i in range(1, len(recent_results)):
            if recent_results[i] == recent_results[i-1]:
                current_streak += 1
            else:
                break
        features.append(current_streak)
        
        # 2. Moving averages (3, 5, 10 periods)
        features.append(np.mean(recent_results[:3]))
        features.append(np.mean(recent_results[:5]))
        features.append(np.mean(recent_results[:10]))
        
        # 3. Balance features
        big_count = sum(recent_results)
        small_count = len(recent_results) - big_count
        features.append(big_count)
        features.append(small_count)
        features.append(big_count - small_count)  # Imbalance
        
        # 4. Number pattern features
        big_numbers = sum(1 for n in recent_numbers if n >= 5)
        small_numbers = len(recent_numbers) - big_numbers
        features.append(big_numbers)
        features.append(small_numbers)
        
        # 5. Alternating pattern score
        alternating_score = 0
        for i in range(1, len(recent_results)):
            if recent_results[i] != recent_results[i-1]:
                alternating_score += 1
        features.append(alternating_score / len(recent_results))
        
        # 6. Gap analysis
        last_big_gap = 0
        last_small_gap = 0
        for i, r in enumerate(recent_results):
            if r == 1:
                last_big_gap = i
                break
        for i, r in enumerate(recent_results):
            if r == 0:
                last_small_gap = i
                break
        features.append(last_big_gap)
        features.append(last_small_gap)
        
        # 7. Number frequency features
        number_counts = [recent_numbers.count(i) for i in range(10)]
        features.extend(number_counts[:3])  # Top 3 frequent numbers
        
        # 8. Pattern type detection
        pattern_hash = self.calculate_pattern_hash(recent_results)
        pattern_type = self.identify_pattern_type(recent_results)
        pattern_score = self.pattern_database.get(pattern_hash, {}).get('success_rate', 0.5)
        features.append(pattern_score)
        
        # 9. Trend features
        if len(recent_results) >= 5:
            trend = np.polyfit(range(5), recent_results[:5], 1)[0]
            features.append(trend)
        else:
            features.append(0)
        
        # 10. Volatility (changes per period)
        changes = sum(1 for i in range(1, len(recent_results)) 
                     if recent_results[i] != recent_results[i-1])
        features.append(changes / len(recent_results))
        
        # Ensure we have exactly feature_count features
        if len(features) < self.feature_count:
            features.extend([0] * (self.feature_count - len(features)))
        elif len(features) > self.feature_count:
            features = features[:self.feature_count]
            
        return features

    def calculate_pattern_hash(self, pattern):
        """Calculate hash for a pattern"""
        pattern_str = ''.join(str(int(x)) for x in pattern)
        return hashlib.md5(pattern_str.encode()).hexdigest()[:10]

    def identify_pattern_type(self, pattern):
        """Identify type of pattern"""
        pattern = list(pattern)
        
        # Check for alternating pattern
        alternating = True
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1]:
                alternating = False
                break
        
        if alternating:
            return 'alternating'
        
        # Check for streak
        streak_count = 1
        max_streak = 1
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1]:
                streak_count += 1
                max_streak = max(max_streak, streak_count)
            else:
                streak_count = 1
        
        if max_streak >= 3:
            return 'streak'
        
        # Check for zigzag (small alternating with occasional same)
        changes = sum(1 for i in range(1, len(pattern)) if pattern[i] != pattern[i-1])
        if changes >= len(pattern) * 0.7:
            return 'zigzag'
        
        # Check for clusters
        clusters = 0
        in_cluster = False
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1] and not in_cluster:
                clusters += 1
                in_cluster = True
            elif pattern[i] != pattern[i-1]:
                in_cluster = False
        
        if clusters >= 2:
            return 'cluster'
        
        return 'random'

    def learn_from_pattern(self, pattern_hash, prediction, was_correct):
        """Learn from pattern outcome"""
        if pattern_hash not in self.pattern_database:
            self.pattern_database[pattern_hash] = {
                'pattern': pattern_hash,
                'total_occurrences': 0,
                'correct_predictions': 0,
                'last_seen': datetime.now().isoformat(),
                'prediction_history': []
            }
        
        pattern_data = self.pattern_database[pattern_hash]
        pattern_data['total_occurrences'] += 1
        
        if was_correct:
            pattern_data['correct_predictions'] += 1
        
        pattern_data['success_rate'] = pattern_data['correct_predictions'] / pattern_data['total_occurrences']
        pattern_data['last_seen'] = datetime.now().isoformat()
        pattern_data['prediction_history'].append({
            'prediction': prediction,
            'was_correct': was_correct,
            'timestamp': datetime.now().isoformat()
        })
        
        # Keep only last 50 predictions in history
        if len(pattern_data['prediction_history']) > 50:
            pattern_data['prediction_history'] = pattern_data['prediction_history'][-50:]
        
        # Update AI statistics
        self.ai_total_predictions += 1
        if was_correct:
            self.ai_correct_predictions += 1
        
        self.ai_accuracy = self.ai_correct_predictions / self.ai_total_predictions if self.ai_total_predictions > 0 else 0
        
        # Save to pattern history
        self.pattern_history.append({
            'pattern_hash': pattern_hash,
            'prediction': prediction,
            'was_correct': was_correct,
            'timestamp': datetime.now().isoformat(),
            'ai_confidence': getattr(self, 'last_ai_confidence', 0.5)
        })
        
        # Keep only last 1000 patterns in history
        if len(self.pattern_history) > 1000:
            self.pattern_history = self.pattern_history[-1000:]
        
        # Retrain AI model periodically
        if self.ai_total_predictions % 50 == 0:
            self.retrain_ai_model()

    def retrain_ai_model(self):
        """Retrain AI model with new data"""
        if len(self.pattern_history) < self.min_training_samples:
            return
        
        try:
            logging.info(f"🔄 Retraining AI model with {len(self.pattern_history)} samples...")
            
            # Prepare training data
            X_train = []
            y_train = []
            
            for pattern_data in self.pattern_history:
                # We need to reconstruct features from pattern history
                # For now, we'll train on simpler features
                if 'features' in pattern_data:
                    X_train.append(pattern_data['features'])
                    y_train.append(1 if pattern_data['was_correct'] else 0)
            
            if len(X_train) < self.min_training_samples:
                return
            
            # Train the model
            X_train_array = np.array(X_train)
            y_train_array = np.array(y_train)
            
            self.scaler.fit(X_train_array)
            X_train_scaled = self.scaler.transform(X_train_array)
            
            self.ai_model.fit(X_train_scaled, y_train_array)
            
            self.ai_learning_cycles += 1
            logging.info(f"✅ AI Model retrained. Learning cycle: {self.ai_learning_cycles}")
            self.save_ai_model()
            
        except Exception as e:
            logging.error(f"❌ Error retraining AI model: {e}")

    def predict_with_ai(self, results, numbers):
        """Make prediction using AI pattern recognition"""
        try:
            if len(results) < self.pattern_window_size:
                return None, 0.5
            
            # Extract features
            features = self.extract_features_for_ai(results, numbers)
            
            if len(features) < self.feature_count:
                return None, 0.5
            
            # Scale features
            features_array = np.array([features])
            
            if hasattr(self.scaler, 'scale_'):
                features_scaled = self.scaler.transform(features_array)
            else:
                features_scaled = features_array
            
            # Make prediction
            if hasattr(self.ai_model, 'predict_proba'):
                proba = self.ai_model.predict_proba(features_scaled)[0]
                prediction_proba = max(proba)
                prediction_class = self.ai_model.predict(features_scaled)[0]
            else:
                # Fallback if model not trained
                return None, 0.5
            
            # Convert to BIG/SMALL prediction
            # Assuming class 1 = BIG, class 0 = SMALL
            prediction = 'BIG' if prediction_class == 1 else 'SMALL'
            
            # Calculate pattern hash for learning
            result_numeric = [1 if r == 'BIG' else 0 for r in results[:self.pattern_window_size]]
            pattern_hash = self.calculate_pattern_hash(result_numeric)
            
            self.last_ai_pattern_used = {
                'pattern_hash': pattern_hash,
                'prediction': prediction,
                'confidence': float(prediction_proba),
                'features': features
            }
            
            return prediction, float(prediction_proba)
            
        except Exception as e:
            logging.error(f"❌ AI Prediction error: {e}")
            return None, 0.5

    def analyze_pattern_with_ai(self, data_list):
        """Analyze pattern using AI + Traditional methods"""
        if not data_list or len(data_list) < 10:
            return random.choice(['BIG', 'SMALL']), 50
        
        recent_data = data_list[:50]  # Use more data for AI
        results = [item['big_small'] for item in recent_data]
        numbers = [item['number'] for item in recent_data]
        
        logging.info(f"🧠 AI Pattern Analysis")
        logging.info(f"Last 10 results: {results[:10]}")
        logging.info(f"Last 10 numbers: {numbers[:10]}")
        
        # Get AI prediction
        ai_prediction, ai_confidence = self.predict_with_ai(results, numbers)
        
        # Get traditional prediction
        patterns = self.detect_winning_patterns(results, numbers)
        strategies = self.calculate_winning_strategies(patterns)
        trad_prediction, trad_confidence = self.combine_winning_strategies(strategies)
        
        # Combine AI and traditional predictions
        final_prediction = None
        final_confidence = 0
        
        if ai_prediction and ai_confidence > self.ai_confidence_threshold:
            # Use AI prediction if confidence is high
            final_prediction = ai_prediction
            final_confidence = ai_confidence * 100
            logging.info(f"🤖 AI Prediction: {ai_prediction} ({ai_confidence:.2%} confidence)")
            
            # Update AI weight based on accuracy
            if self.ai_accuracy > 0.7:
                self.pattern_weights['ai_pattern'] = 0.55
            else:
                self.pattern_weights['ai_pattern'] = 0.45
                
        else:
            # Fall back to traditional prediction
            final_prediction = trad_prediction
            final_confidence = trad_confidence
            logging.info(f"📊 Traditional Prediction: {trad_prediction} ({trad_confidence:.1f}%)")
        
        # Safety checks
        if self.consecutive_losses >= 3:
            logging.info(f"🔴 CRITICAL: {self.consecutive_losses} consecutive losses!")
            if final_prediction == 'BIG':
                final_prediction = 'SMALL'
                final_confidence = 75
            else:
                final_prediction = 'BIG'
                final_confidence = 75
        
        # Don't predict same thing too many times
        recent_predictions = list(self.big_small_history)
        if len(recent_predictions) >= 5:
            recent_predictions = recent_predictions[-5:]
            if all(p == final_prediction for p in recent_predictions):
                logging.info(f"⚠️ Too many consecutive {final_prediction} predictions, flipping...")
                final_prediction = 'BIG' if final_prediction == 'SMALL' else 'SMALL'
                final_confidence = max(60, final_confidence - 10)
        
        # Store prediction in history
        self.big_small_history.append(final_prediction)
        
        # Update statistics
        self.last_ai_confidence = ai_confidence if ai_prediction else 0
        
        logging.info(f"🎯 FINAL PREDICTION: {final_prediction} ({final_confidence:.1f}%)")
        logging.info(f"📈 AI Accuracy: {self.ai_accuracy:.2%}")
        logging.info("=" * 60)
        
        return final_prediction, final_confidence

    def initialize_configs(self):
        """Initialize all configurations properly"""
        # First load emoji config
        self.load_emoji_config()
        
        # Then load main config
        self.load_config()
        
        # Ensure emoji config has all required keys
        self.ensure_emoji_config_keys()

    def ensure_emoji_config_keys(self):
        """Ensure all required keys exist in emoji config"""
        if not hasattr(self, 'emoji_config'):
            self.load_emoji_config()
        
        required_keys = ['premium_emojis', 'regular_emojis', 'emoji_to_placeholder', 'placeholder_to_emoji']
        
        for key in required_keys:
            if key not in self.emoji_config:
                if key == 'emoji_to_placeholder':
                    self.emoji_config[key] = {
                        "🔥": "{fire}",
                        "👑": "{crown}",
                        "✨": "{sparkles}",
                        "🚀": "{rocket}",
                        "💰": "{money}",
                        "📊": "{chart}",
                        "🎯": "{target}",
                        "🏆": "{trophy}",
                        "🎁": "{gift}",
                        "⚡": "{lightning}",
                        "⭐": "{star}",
                        "⚠️": "{warning}",
                        "✅": "{check}",
                        "❌": "{cross}",
                        "⏰": "{clock}",
                        "🔗": "{link}",
                        "🌙": "{moon}",
                        "🌅": "{sun}",
                        "☕": "{coffee}",
                        "💤": "{sleep}",
                        "⏸️": "{break_icon}",
                        "🔄": "{reload}",
                        "🎉": "{party}",
                        "💸": "{money_loss}",
                        "🌟": "{star2}"
                    }
                elif key == 'placeholder_to_emoji':
                    self.emoji_config[key] = {
                        "{fire}": "🔥",
                        "{crown}": "👑",
                        "{sparkles}": "✨",
                        "{rocket}": "🚀",
                        "{money}": "💰",
                        "{chart}": "📊",
                        "{target}": "🎯",
                        "{trophy}": "🏆",
                        "{gift}": "🎁",
                        "{lightning}": "⚡",
                        "{star}": "⭐",
                        "{warning}": "⚠️",
                        "{check}": "✅",
                        "{cross}": "❌",
                        "{clock}": "⏰",
                        "{link}": "🔗",
                        "{moon}": "🌙",
                        "{sun}": "🌅",
                        "{coffee}": "☕",
                        "{sleep}": "💤",
                        "{break_icon}": "⏸️",
                        "{reload}": "🔄",
                        "{party}": "🎉",
                        "{money_loss}": "💸",
                        "{star2}": "🌟"
                    }
                elif key not in self.emoji_config:
                    self.emoji_config[key] = {}
        
        self.save_emoji_config()

    def format_promo_text_with_emojis(self, text, for_channel=False):
        """Format promotional text with emojis"""
        if not text:
            return ""
        
        try:
            # First, auto-convert any regular emojis to placeholders
            text = self.auto_detect_and_convert_message(text)
            
            # Then convert placeholders to appropriate emojis
            return self.convert_placeholder_to_premium_emoji(text, for_channel)
        except Exception as e:
            logging.error(f"❌ Error formatting promo text: {e}")
            return text

    def load_emoji_config(self):
        """Load emoji configurations from separate file"""
        default_emoji_config = {
            "premium_emojis": {
                "fire": "<emoji id=5420315771991497307>🔥</emoji>",
                "crown": "<emoji id=6266995104687330978>👑</emoji>",
                "sparkles": "<emoji id=6285088169817805553>✨</emoji>",
                "rocket": "<emoji id=5188481279963715781>🚀</emoji>",
                "money": "<emoji id=6267068789146260253>💰</emoji>",
                "chart": "<emoji id=5431577498364158238>📊</emoji>",
                "target": "<emoji id=5310278924616356636>🎯</emoji>",
                "trophy": "<emoji id=5413566144986503832>🏆</emoji>",
                "gift": "<emoji id=5384578448633129482>🎁</emoji>",
                "lightning": "<emoji id=6267107057304868214>⚡</emoji>",
                "star": "<emoji id=5435957248314579621>⭐</emoji>",
                "warning": "<emoji id=6267039884016358504>⚠️</emoji>",
                "check": "<emoji id=6267008582294705964>✅</emoji>",
                "cross": "<emoji id=5343968063970632884>❌</emoji>",
                "clock": "<emoji id=5386415655253730366>⏰</emoji>",
                "link": "<emoji id=4958689671950369798>🔗</emoji>",
                "moon": "<emoji id=5208554136039073738>🌙</emoji>",
                "sun": "<emoji id=5413883478645169306>🌅</emoji>",
                "coffee": "<emoji id=5451959871257713464>☕</emoji>",
                "sleep": "<emoji id=5359543311897998264>💤</emoji>",
                "break_icon": "<emoji id=5359543311897998264>⏸️</emoji>",
                "reload": "<emoji id=5264727218734524899>🔄</emoji>",
                "party": "<emoji id=5436040291507247633>🎉</emoji>",
                "money_loss": "<emoji id=5472030678633684592>💸</emoji>",
                "star2": "<emoji id=5458799228719472718>🌟</emoji>",
            },
            "regular_emojis": {
                "fire": "🔥",
                "crown": "👑",
                "sparkles": "✨",
                "rocket": "🚀",
                "money": "💰",
                "chart": "📊",
                "target": "🎯",
                "trophy": "🏆",
                "gift": "🎁",
                "lightning": "⚡",
                "star": "⭐",
                "warning": "⚠️",
                "check": "✅",
                "cross": "❌",
                "clock": "⏰",
                "link": "🔗",
                "moon": "🌙",
                "sun": "🌅",
                "coffee": "☕",
                "sleep": "💤",
                "break_icon": "⏸️",
                "reload": "🔄",
                "party": "🎉",
                "money_loss": "💸",
                "star2": "🌟"
            },
            "emoji_to_placeholder": {
                "🔥": "{fire}",
                "👑": "{crown}",
                "✨": "{sparkles}",
                "🚀": "{rocket}",
                "💰": "{money}",
                "📊": "{chart}",
                "🎯": "{target}",
                "🏆": "{trophy}",
                "🎁": "{gift}",
                "⚡": "{lightning}",
                "⭐": "{star}",
                "⚠️": "{warning}",
                "✅": "{check}",
                "❌": "{cross}",
                "⏰": "{clock}",
                "🔗": "{link}",
                "🌙": "{moon}",
                "🌅": "{sun}",
                "☕": "{coffee}",
                "💤": "{sleep}",
                "⏸️": "{break_icon}",
                "🔄": "{reload}",
                "🎉": "{party}",
                "💸": "{money_loss}",
                "🌟": "{star2}"
            },
            "placeholder_to_emoji": {
                "{fire}": "🔥",
                "{crown}": "👑",
                "{sparkles}": "✨",
                "{rocket}": "🚀",
                "{money}": "💰",
                "{chart}": "📊",
                "{target}": "🎯",
                "{trophy}": "🏆",
                "{gift}": "🎁",
                "{lightning}": "⚡",
                "{star}": "⭐",
                "{warning}": "⚠️",
                "{check}": "✅",
                "{cross}": "❌",
                "{clock}": "⏰",
                "{link}": "🔗",
                "{moon}": "🌙",
                "{sun}": "🌅",
                "{coffee}": "☕",
                "{sleep}": "💤",
                "{break_icon}": "⏸️",
                "{reload}": "🔄",
                "{party}": "🎉",
                "{money_loss}": "💸",
                "{star2}": "🌟"
            }
        }
        
        try:
            if os.path.exists(self.emoji_config_file):
                with open(self.emoji_config_file, 'r', encoding='utf-8') as f:
                    self.emoji_config = json.load(f)
                logging.info("✅ Emoji configuration loaded from file")
            else:
                self.emoji_config = default_emoji_config
                self.save_emoji_config()
                logging.info("✅ Created default emoji configuration file")
        except Exception as e:
            logging.error(f"❌ Error loading emoji config: {e}")
            self.emoji_config = default_emoji_config
            self.save_emoji_config()
        
        self.ensure_emoji_config_keys()

    def save_emoji_config(self):
        """Save emoji configuration"""
        try:
            self.mongo.meta.update_one({'_id':'emoji_config'},{'$set':{'data':self.emoji_config}},upsert=True)
            logging.info("✅ Emoji configuration saved")
        except Exception as e:
            logging.error(f"❌ Error saving emoji config: {e}")

    def get_emoji(self, emoji_key, for_channel=False):
        """Get emoji"""
        try:
            if for_channel and self.use_user_account:
                return self.emoji_config['premium_emojis'].get(emoji_key, self.emoji_config['regular_emojis'].get(emoji_key, ''))
            else:
                return self.emoji_config['regular_emojis'].get(emoji_key, '')
        except KeyError:
            regular_emojis = {
                "fire": "🔥", "crown": "👑", "sparkles": "✨", "rocket": "🚀",
                "money": "💰", "chart": "📊", "target": "🎯", "trophy": "🏆",
                "gift": "🎁", "lightning": "⚡", "star": "⭐", "warning": "⚠️",
                "check": "✅", "cross": "❌", "clock": "⏰", "link": "🔗",
                "moon": "🌙", "sun": "🌅", "coffee": "☕", "sleep": "💤",
                "break_icon": "⏸️", "reload": "🔄", "party": "🎉", "money_loss": "💸", "star2": "🌟"
            }
            return regular_emojis.get(emoji_key, '')

    def convert_regular_emoji_to_placeholder(self, text):
        """Convert regular emojis in text to placeholders for storage"""
        if not text:
            return text
        
        try:
            if 'emoji_to_placeholder' not in self.emoji_config:
                self.ensure_emoji_config_keys()
            
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if emoji in text:
                    text = text.replace(emoji, placeholder)
        
        except Exception as e:
            logging.error(f"❌ Error converting emojis to placeholders: {e}")
            pass
        
        return text

    def convert_placeholder_to_premium_emoji(self, text, for_channel=False):
        """Convert placeholders in text to premium emojis for sending"""
        if not text:
            return text
        
        try:
            if 'placeholder_to_emoji' not in self.emoji_config:
                self.ensure_emoji_config_keys()
            
            if not for_channel or not self.use_user_account:
                for placeholder, emoji in self.emoji_config['placeholder_to_emoji'].items():
                    if placeholder in text:
                        text = text.replace(placeholder, emoji)
                return text
            
            if for_channel and self.use_user_account:
                for placeholder, premium_emoji in self.emoji_config['premium_emojis'].items():
                    placeholder_format = f"{{{placeholder}}}"
                    if placeholder_format in text:
                        text = text.replace(placeholder_format, premium_emoji)
            
            if 'placeholder_to_emoji' in self.emoji_config:
                for placeholder, emoji in self.emoji_config['placeholder_to_emoji'].items():
                    if placeholder in text:
                        text = text.replace(placeholder, emoji)
        
        except Exception as e:
            logging.error(f"❌ Error converting placeholders to emojis: {e}")
            basic_replacements = {
                "{fire}": "🔥", "{crown}": "👑", "{sparkles}": "✨", "{rocket}": "🚀",
                "{money}": "💰", "{chart}": "📊", "{target}": "🎯", "{trophy}": "🏆",
                "{gift}": "🎁", "{lightning}": "⚡", "{star}": "⭐", "{warning}": "⚠️",
                "{check}": "✅", "{cross}": "❌", "{clock}": "⏰", "{link}": "🔗",
                "{moon}": "🌙", "{sun}": "🌅", "{coffee}": "☕", "{sleep}": "💤",
                "{break_icon}": "⏸️", "{reload}": "🔄", "{party}": "🎉", "{money_loss}": "💸", "{star2}": "🌟"
            }
            for placeholder, emoji in basic_replacements.items():
                if placeholder in text:
                    text = text.replace(placeholder, emoji)
        
        return text

    def format_with_emojis(self, text, for_channel=False):
        """Convert stored text with placeholders to emojis for sending"""
        return self.convert_placeholder_to_premium_emoji(text, for_channel)

    def extract_emojis_from_text(self, text):
        """Extract all emojis from text and convert to placeholders"""
        if not text:
            return text, []
        
        emojis_found = []
        placeholder_text = text
        
        try:
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if emoji in text:
                    emojis_found.append(emoji)
                    placeholder_text = placeholder_text.replace(emoji, placeholder)
        except Exception as e:
            logging.error(f"❌ Error extracting emojis: {e}")
        
        return placeholder_text, emojis_found

    def auto_detect_and_convert_message(self, message_text):
        """Automatically detect emojis in message and convert for storage"""
        if not message_text:
            return message_text
        
        try:
            if 'emoji_to_placeholder' not in self.emoji_config:
                self.ensure_emoji_config_keys()
            
            converted_text = message_text
            
            emojis_found = []
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if emoji in converted_text:
                    emojis_found.append(f"{emoji}->{placeholder}")
                    converted_text = converted_text.replace(emoji, placeholder)
            
            if emojis_found:
                logging.info(f"✅ Auto-converted emojis: {', '.join(emojis_found[:5])}{'...' if len(emojis_found) > 5 else ''}")
            
            import emoji
            emoji_list = emoji.emoji_list(message_text)
            for emoji_data in emoji_list:
                emoji_char = emoji_data['emoji']
                if emoji_char not in self.emoji_config['emoji_to_placeholder']:
                    emoji_name = emoji.demojize(emoji_char).replace(':', '').replace('_', '')
                    placeholder = f"{{{emoji_name}}}"
                    
                    self.emoji_config['emoji_to_placeholder'][emoji_char] = placeholder
                    self.emoji_config['placeholder_to_emoji'][placeholder] = emoji_char
                    self.emoji_config['regular_emojis'][emoji_name] = emoji_char
                    
                    premium_emojis = {
                        "🔥": "<emoji id=5420315771991497307>🔥</emoji>",
                        "👑": "<emoji id=6266995104687330978>👑</emoji>",
                        "✨": "<emoji id=6285088169817805553>✨</emoji>",
                        "🚀": "<emoji id=5188481279963715781>🚀</emoji>",
                        "💰": "<emoji id=6267068789146260253>💰</emoji>",
                        "📊": "<emoji id=5431577498364158238>📊</emoji>",
                        "🎯": "<emoji id=5310278924616356636>🎯</emoji>",
                        "🏆": "<emoji id=5413566144986503832>🏆</emoji>",
                        "🎁": "<emoji id=5384578448633129482>🎁</emoji>",
                        "⚡": "<emoji id=6267107057304868214>⚡</emoji>",
                        "⭐": "<emoji id=5435957248314579621>⭐</emoji>",
                        "⚠️": "<emoji id=6267039884016358504>⚠️</emoji>",
                        "✅": "<emoji id=6267008582294705964>✅</emoji>",
                        "❌": "<emoji id=5343968063970632884>❌</emoji>",
                        "⏰": "<emoji id=5386415655253730366>⏰</emoji>",
                        "🔗": "<emoji id=4958689671950369798>🔗</emoji>",
                        "🌙": "<emoji id=5208554136039073738>🌙</emoji>",
                        "🌅": "<emoji id=5413883478645169306>🌅</emoji>",
                        "☕": "<emoji id=5451959871257713464>☕</emoji>",
                        "💤": "<emoji id=5359543311897998264>💤</emoji>",
                        "⏸️": "<emoji id=5359543311897998264>⏸️</emoji>",
                        "🔄": "<emoji id=5264727218734524899>🔄</emoji>",
                        "🎉": "<emoji id=5436040291507247633>🎉</emoji>",
                        "💸": "<emoji id=5472030678633684592>💸</emoji>",
                        "🌟": "<emoji id=5458799228719472718>🌟</emoji>",
                    }
                    if emoji_char in premium_emojis:
                        self.emoji_config['premium_emojis'][emoji_name] = premium_emojis[emoji_char]
                    
                    logging.info(f"✅ Auto-added new emoji: {emoji_char} -> {placeholder}")
                    converted_text = converted_text.replace(emoji_char, placeholder)
            
            self.save_emoji_config()
            return converted_text
            
        except Exception as e:
            logging.error(f"❌ Error in auto-detect and convert: {e}")
            return message_text

    async def initialize_user_client(self):
        """Initialize Pyrogram user client"""
        if not self.use_user_account:
            logging.warning("User account not configured. Using regular emojis.")
            return False
        
        try:
            session_exists = os.path.exists("user_session.session")
            
            self.user_app = Client(
                "user_session",
                api_id=self.api_id,
                api_hash=self.api_hash,
                phone_number=self.phone,
                in_memory=False
            )
            
            await self.user_app.start()
            
            me = await self.user_app.get_me()
            logging.info(f"✅ User account connected: {me.first_name} (@{me.username})")
            
            if hasattr(me, 'is_premium') and me.is_premium:
                logging.info("✅ Premium account detected!")
            
            await self.resolve_all_channels()
            
            return True
            
        except Exception as e:
            logging.error(f"❌ Failed to initialize user account: {e}")
            self.use_user_account = False
            return False

    async def resolve_all_channels(self):
        """Resolve all channel peers"""
        if not self.user_app or not self.active_channels:
            return
        
        logging.info("🔍 Resolving all channels...")
        
        for channel in self.active_channels:
            try:
                if channel in self.failed_peers:
                    continue
                    
                if channel.startswith('@'):
                    chat = await self.user_app.get_chat(channel)
                    self.resolved_peers[channel] = chat.id
                    logging.info(f"✅ Resolved {channel} -> {chat.id}")
                elif channel.lstrip('-').isdigit():
                    channel_id = int(channel)
                    try:
                        chat = await self.user_app.get_chat(channel_id)
                        self.resolved_peers[channel] = channel_id
                        logging.info(f"✅ Verified channel ID: {channel} -> {chat.title}")
                    except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
                        logging.warning(f"⚠️ Cannot access channel {channel}: {e}")
                        self.failed_peers.add(channel)
                
            except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
                logging.error(f"❌ Cannot access channel {channel}: {e}")
                self.failed_peers.add(channel)
                continue
            except Exception as e:
                logging.error(f"❌ Failed to resolve {channel}: {e}")
                self.failed_peers.add(channel)
                continue

    async def download_media_for_user_account(self, file_id, context: ContextTypes.DEFAULT_TYPE):
        """Download media file for user account sending"""
        try:
            file = await context.bot.get_file(file_id)
            file_bytes = await file.download_as_bytearray()
            file_stream = BytesIO(file_bytes)
            
            if hasattr(file, 'file_path'):
                filename = file.file_path.split('/')[-1] if file.file_path else f"media_{file_id}"
            else:
                filename = f"media_{file_id}"
            
            if '.' not in filename:
                filename = f"{filename}.jpg"
            
            file_stream.name = filename
            return file_stream
            
        except Exception as e:
            logging.error(f"❌ Failed to download media for user account: {e}")
            return None

    async def send_via_user_account(self, chat_id, text=None, media_type=None, media_file=None, caption=None, media_group=None, context=None):
        """Send message using Pyrogram"""
        if not self.user_app:
            return False
        
        if chat_id in self.failed_peers:
            logging.info(f"⚠️ Skipping failed peer: {chat_id}")
            return False
        
        try:
            target_id = None
            
            if chat_id in self.resolved_peers:
                target_id = self.resolved_peers[chat_id]
            else:
                try:
                    if str(chat_id).startswith('@'):
                        chat = await self.user_app.get_chat(chat_id)
                        target_id = chat.id
                        self.resolved_peers[chat_id] = target_id
                    elif str(chat_id).lstrip('-').isdigit():
                        target_id = int(chat_id)
                        try:
                            await self.user_app.get_chat(target_id)
                        except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant):
                            logging.warning(f"⚠️ Channel {target_id} may not be accessible")
                            self.failed_peers.add(chat_id)
                            return False
                        self.resolved_peers[chat_id] = target_id
                    else:
                        logging.error(f"❌ Invalid channel format: {chat_id}")
                        return False
                except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
                    logging.error(f"❌ Cannot access channel {chat_id}: {e}")
                    self.failed_peers.add(chat_id)
                    return False
            
            if media_group and len(media_group) > 1:
                logging.info(f"📸 Sending media group with {len(media_group)} items to {chat_id}")
                
                pyrogram_media = []
                for i, media_item in enumerate(media_group):
                    file_stream = await self.download_media_for_user_account(media_item['media'], context)
                    if not file_stream:
                        logging.error(f"❌ Failed to download media for user account: {media_item['media']}")
                        continue
                    
                    if media_item['type'] == 'photo':
                        media = PyrogramInputMediaPhoto(
                            media=file_stream,
                            caption=media_item.get('caption', '') if i == 0 else None,
                            parse_mode=PyrogramParseMode.HTML if media_item.get('caption') else None
                        )
                    elif media_item['type'] == 'video':
                        media = PyrogramInputMediaVideo(
                            media=file_stream,
                            caption=media_item.get('caption', '') if i == 0 else None,
                            parse_mode=PyrogramParseMode.HTML if media_item.get('caption') else None
                        )
                    elif media_item['type'] == 'document':
                        media = PyrogramInputMediaDocument(
                            media=file_stream,
                            caption=media_item.get('caption', '') if i == 0 else None,
                            parse_mode=PyrogramParseMode.HTML if media_item.get('caption') else None
                        )
                    elif media_item['type'] == 'animation':
                        media = PyrogramInputMediaVideo(
                            media=file_stream,
                            caption=media_item.get('caption', '') if i == 0 else None,
                            parse_mode=PyrogramParseMode.HTML if media_item.get('caption') else None
                        )
                    pyrogram_media.append(media)
                
                if pyrogram_media:
                    await self.user_app.send_media_group(
                        chat_id=target_id,
                        media=pyrogram_media
                    )
                    logging.info(f"✅ Media group sent via user account to {chat_id}")
                    return True
                else:
                    logging.error("❌ No valid media items to send")
                    return False
                
            elif media_type and media_file:
                file_stream = await self.download_media_for_user_account(media_file, context)
                if not file_stream:
                    logging.error(f"❌ Failed to download media for user account: {media_file}")
                    return False
                
                if media_type == 'photo':
                    await self.user_app.send_photo(
                        chat_id=target_id,
                        photo=file_stream,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'video':
                    await self.user_app.send_video(
                        chat_id=target_id,
                        video=file_stream,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'document':
                    await self.user_app.send_document(
                        chat_id=target_id,
                        document=file_stream,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'animation':
                    await self.user_app.send_animation(
                        chat_id=target_id,
                        animation=file_stream,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                logging.info(f"✅ Media sent via user account to {chat_id}")
                return True
                
            else:
                if not text or not text.strip():
                    logging.error("❌ Text is empty!")
                    return False
                    
                await self.user_app.send_message(
                    chat_id=target_id,
                    text=text,
                    parse_mode=PyrogramParseMode.HTML
                )
                logging.info(f"✅ Text sent via user account to {chat_id}")
                return True
            
        except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
            logging.error(f"❌ Cannot access channel {chat_id}: {e}")
            self.failed_peers.add(chat_id)
            if chat_id in self.resolved_peers:
                del self.resolved_peers[chat_id]
            return False
            
        except FloodWait as e:
            logging.warning(f"⚠️ FloodWait: Waiting {e.value}s")
            await asyncio.sleep(e.value)
            return False
            
        except Exception as e:
            logging.error(f"❌ User account send failed for {chat_id}: {e}")
            self.failed_peers.add(chat_id)
            return False

    async def send_message_with_retry(self, context: ContextTypes.DEFAULT_TYPE, chat_id, text=None, max_retries=3, for_channel=False, media_type=None, media_file=None, caption=None, media_group=None):
        """Send message with retry logic"""
        
        if chat_id in self.failed_peers:
            for_channel = False
            logging.info(f"⚠️ Using bot for failed peer: {chat_id}")
        
        for attempt in range(max_retries):
            try:
                if media_group and len(media_group) > 1:
                    logging.info(f"📸 Sending media group with {len(media_group)} items via bot to {chat_id}")
                    
                    telegram_media = []
                    for i, media_item in enumerate(media_group):
                        caption_text = media_item.get('caption', '')
                        
                        if caption_text:
                            if for_channel and self.use_user_account:
                                caption_text = self.format_with_emojis(caption_text, for_channel=True)
                            else:
                                caption_text = self.format_with_emojis(caption_text, for_channel=False)
                        
                        if media_item['type'] == 'photo':
                            media = InputMediaPhoto(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        elif media_item['type'] == 'video':
                            media = InputMediaVideo(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        elif media_item['type'] == 'document':
                            media = InputMediaDocument(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        telegram_media.append(media)
                    
                    if for_channel and self.use_user_account and self.user_app:
                        success = await self.send_via_user_account(
                            chat_id, None, None, None, None, media_group, context
                        )
                        if success:
                            return True
                        else:
                            logging.warning("⚠️ User account failed, using bot fallback")
                    
                    result = await context.bot.send_media_group(
                        chat_id=chat_id,
                        media=telegram_media
                    )
                    logging.info(f"✅ Media group sent to {chat_id}")
                    return result
                    
                elif media_type and media_file:
                    if caption:
                        if for_channel and self.use_user_account:
                            caption = self.format_with_emojis(caption, for_channel=True)
                        else:
                            caption = self.format_with_emojis(caption, for_channel=False)
                    
                    if for_channel and self.use_user_account and self.user_app:
                        success = await self.send_via_user_account(
                            chat_id, None, media_type, media_file, caption, None, context
                        )
                        if success:
                            return True
                        else:
                            logging.warning("⚠️ User account failed, using bot fallback")
                    
                    if media_type == 'photo':
                        result = await context.bot.send_photo(
                            chat_id=chat_id,
                            photo=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    elif media_type == 'video':
                        result = await context.bot.send_video(
                            chat_id=chat_id,
                            video=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    elif media_type == 'document':
                        result = await context.bot.send_document(
                            chat_id=chat_id,
                            document=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    elif media_type == 'animation':
                        result = await context.bot.send_animation(
                            chat_id=chat_id,
                            animation=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    logging.info(f"✅ Media sent to {chat_id}")
                    return result
                    
                else:
                    if not text or not text.strip():
                        logging.error("❌ Text is empty!")
                        return False
                    
                    final_text = text
                    if for_channel and self.use_user_account:
                        final_text = self.format_with_emojis(text, for_channel=True)
                    else:
                        final_text = self.format_with_emojis(text, for_channel=False)
                    
                    if for_channel and self.use_user_account and self.user_app:
                        success = await self.send_via_user_account(
                            chat_id, final_text, None, None, None, None, context
                        )
                        if success:
                            return True
                        else:
                            logging.warning("⚠️ User account failed, using bot fallback")
                    
                    import re
                    clean_text = re.sub(r'<emoji id=\d+>([^<]+)</emoji>', r'\1', final_text)
                    
                    if not clean_text or not clean_text.strip():
                        logging.error("❌ Clean text is empty!")
                        return False
                    
                    result = await context.bot.send_message(
                        chat_id=chat_id,
                        text=clean_text,
                        parse_mode=None
                    )
                    logging.info(f"✅ Text message sent to {chat_id}")
                    return result
                
            except NetworkError as e:
                logging.warning(f"⚠️ Network error on attempt {attempt + 1}/{max_retries}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                    
            except TimedOut as e:
                logging.warning(f"⚠️ Timeout on attempt {attempt + 1}/{max_retries}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                    
            except RetryAfter as e:
                logging.warning(f"⚠️ Rate limited, waiting {e.retry_after}s")
                await asyncio.sleep(e.retry_after)
                
            except Exception as e:
                logging.error(f"❌ Error sending message to {chat_id}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
        
        return False

    def load_config(self):
        """Load configuration with channel-specific settings"""
        default_config = {
            "admin_ids": [6484788124],
            "channels": [],
            "channel_configs": {},
            "channel_prediction_status": {},
            "custom_break_messages": {},
            "custom_break_schedules": {},
            "api_url": "https://draw.ar-lottery01.com/WinGo/WinGo_1M/GetHistoryIssuePage.json"
        }
        
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    loaded_config = json.load(f)
                    self.config = {**default_config, **loaded_config}
                
                self.active_channels = self.config.get('channels', [])
                self.channel_configs = self.config.get('channel_configs', {})
                self.channel_prediction_status = self.config.get('channel_prediction_status', {})
                self.custom_break_messages = self.config.get('custom_break_messages', {})
                self.custom_break_schedules = self.config.get('custom_break_schedules', {})
                
                # Ensure all channel configs have templates and prediction status
                for channel_id, config in self.channel_configs.items():
                    if 'templates' not in config:
                        config['templates'] = self.default_templates.copy()
                    if 'show_links' not in config:
                        config['show_links'] = True
                    if 'show_promo' not in config:
                        config['show_promo'] = True
                    # Initialize prediction status if not exists
                    if channel_id not in self.channel_prediction_status:
                        self.channel_prediction_status[channel_id] = True
                
                logging.info(f"✅ Configuration loaded. Active channels: {len(self.active_channels)}")
                logging.info(f"✅ Channel prediction status loaded for {len(self.channel_prediction_status)} channels")
                
                # Fix custom_break_messages structure
                for channel_id, messages in self.custom_break_messages.items():
                    if isinstance(messages, dict):
                        self.custom_break_messages[channel_id] = [messages]
                    elif not isinstance(messages, list):
                        self.custom_break_messages[channel_id] = []
                
                total_msgs = sum(len(msgs) for msgs in self.custom_break_messages.values() if isinstance(msgs, list))
                logging.info(f"✅ Custom break messages: {total_msgs} across {len(self.custom_break_messages)} channels")
                
            else:
                self.config = default_config
                self.active_channels = []
                self.channel_configs = {}
                self.channel_prediction_status = {}
                self.custom_break_messages = {}
                self.custom_break_schedules = {}
                self.save_config()
                logging.info("✅ Created new config file")
        except Exception as e:
            logging.error(f"❌ Error loading config: {e}")
            self.config = default_config
            self.active_channels = []
            self.channel_configs = {}
            self.channel_prediction_status = {}
            self.custom_break_messages = {}
            self.custom_break_schedules = {}
            self.save_config()

    def save_config(self):
        """Save configuration"""
        try:
            self.config['channels'] = self.active_channels
            self.config['channel_configs'] = self.channel_configs
            self.config['channel_prediction_status'] = self.channel_prediction_status
            self.config['custom_break_messages'] = self.custom_break_messages
            self.config['custom_break_schedules'] = self.custom_break_schedules
            self.mongo.meta.update_one({'_id':'wingo_config'},{'$set':{'data':self.config}},upsert=True)
            logging.info(f"✅ Configuration saved. Active channels: {len(self.active_channels)}")
        except Exception as e:
            logging.error(f"❌ Error saving config: {e}")

    def get_channel_config(self, channel_id):
        """Get channel-specific config or create default"""
        if channel_id not in self.channel_configs:
            self.channel_configs[channel_id] = {
                'register_link': "https://example.com/register",
                'promotional_text': "{gift} Register now and get DAILY FREE GIFT CODE! {gift}",
                'show_links': True,
                'show_promo': True,
                'templates': self.default_templates.copy(),
                'custom_break_enabled': False,
                'custom_break_delay': 5,
                'custom_break_mode': 'sequential',
            }
            self.save_config()
        
        config = self.channel_configs[channel_id]
        if 'show_links' not in config:
            config['show_links'] = True
        if 'show_promo' not in config:
            config['show_promo'] = True
        if 'templates' not in config:
            config['templates'] = self.default_templates.copy()
            self.save_config()
        if 'custom_break_mode' not in config:
            config['custom_break_mode'] = 'sequential'
            self.save_config()
        
        return config

    def update_channel_config(self, channel_id, updates):
        """Update channel-specific config"""
        config = self.get_channel_config(channel_id)
        
        if 'templates' in updates:
            config['templates'].update(updates['templates'])
            del updates['templates']
        
        config.update(updates)
        self.channel_configs[channel_id] = config
        self.save_config()
        return config

    def get_channel_template(self, channel_id, template_key):
        """Get template for specific channel"""
        config = self.get_channel_config(channel_id)
        return config['templates'].get(template_key, self.default_templates.get(template_key, ''))

    def is_channel_prediction_active(self, channel_id):
        """Check if predictions are active for a channel"""
        return self.channel_prediction_status.get(channel_id, True)

    def toggle_channel_prediction(self, channel_id):
        """Toggle prediction status for a channel"""
        current_status = self.is_channel_prediction_active(channel_id)
        self.channel_prediction_status[channel_id] = not current_status
        self.save_config()
        return self.channel_prediction_status[channel_id]

    def set_channel_prediction_status(self, channel_id, status):
        """Set prediction status for a channel"""
        self.channel_prediction_status[channel_id] = status
        self.save_config()
        return status

    def get_custom_break_messages(self, channel_id):
        """Get ALL custom break messages for channel"""
        messages = self.custom_break_messages.get(channel_id, [])
        if isinstance(messages, dict):
            messages = [messages]
        elif not isinstance(messages, list):
            messages = []
        return messages

    def get_custom_break_message_by_index(self, channel_id, index):
        """Get specific custom break message by index"""
        messages = self.get_custom_break_messages(channel_id)
        if 0 <= index < len(messages):
            return messages[index]
        return None

    def add_custom_break_message(self, channel_id, message_data):
        """Add a new custom break message for channel"""
        if channel_id not in self.custom_break_messages:
            self.custom_break_messages[channel_id] = []
        
        if not isinstance(self.custom_break_messages[channel_id], list):
            self.custom_break_messages[channel_id] = []
        
        self.custom_break_messages[channel_id].append(message_data)
        self.save_config()
        logging.info(f"✅ Custom break message added for {channel_id}. Total: {len(self.custom_break_messages[channel_id])}")
        return len(self.custom_break_messages[channel_id]) - 1

    def update_custom_break_message(self, channel_id, index, message_data):
        """Update existing custom break message"""
        messages = self.get_custom_break_messages(channel_id)
        if 0 <= index < len(messages):
            self.custom_break_messages[channel_id][index] = message_data
            self.save_config()
            logging.info(f"✅ Custom break message updated for {channel_id} at index {index}")
            return True
        return False

    def delete_custom_break_message(self, channel_id, index=None):
        """Delete custom break message(s) for channel"""
        if channel_id in self.custom_break_messages:
            if index is None:
                del self.custom_break_messages[channel_id]
                self.save_config()
                logging.info(f"✅ All custom break messages deleted for {channel_id}")
                return True
            elif isinstance(self.custom_break_messages[channel_id], list) and 0 <= index < len(self.custom_break_messages[channel_id]):
                deleted = self.custom_break_messages[channel_id].pop(index)
                if not self.custom_break_messages[channel_id]:
                    del self.custom_break_messages[channel_id]
                self.save_config()
                logging.info(f"✅ Custom break message deleted for {channel_id} at index {index}")
                return True
        return False

    def get_next_custom_break_index(self, channel_id):
        """Get the next custom break message index to send"""
        channel_config = self.get_channel_config(channel_id)
        
        if channel_id not in self.custom_break_schedules:
            self.custom_break_schedules[channel_id] = 0
            self.save_config()
        
        messages = self.get_custom_break_messages(channel_id)
        if not messages:
            return None
        
        mode = channel_config.get('custom_break_mode', 'sequential')
        
        if mode == 'sequential':
            current_idx = self.custom_break_schedules[channel_id]
            self.custom_break_schedules[channel_id] = (current_idx + 1) % len(messages)
            self.save_config()
            return current_idx
        else:
            return random.randint(0, len(messages) - 1)

    def format_custom_message_with_premium_emojis(self, text, channel_id):
        """Format custom message text with premium emojis"""
        if not text:
            return text
        
        try:
            text = self.auto_detect_and_convert_message(text)
            return self.convert_placeholder_to_premium_emoji(text, for_channel=True)
        except Exception as e:
            logging.error(f"❌ Error formatting custom message: {e}")
            return text

    def format_session_message(self, channel_id, for_channel=False):
        """Format session message with channel-specific config"""
        if not self.session_predictions:
            return ""
        
        try:
            channel_config = self.get_channel_config(channel_id)
            
            header = self.get_channel_template(channel_id, 'prediction_header')
            session_line_template = self.get_channel_template(channel_id, 'session_line')
            maintain = self.get_channel_template(channel_id, 'maintain_level')
            footer_template = self.get_channel_template(channel_id, 'prediction_footer')
            
            header = self.format_with_emojis(header, for_channel)
            session_line_template = self.format_with_emojis(session_line_template, for_channel)
            maintain = self.format_with_emojis(maintain, for_channel)
            footer_template = self.format_with_emojis(footer_template, for_channel)
            
            try:
                session_line = session_line_template.format(session=self.current_session)
            except KeyError as e:
                logging.warning(f"⚠️ KeyError in session_line: {e}")
                session_line = session_line_template
            
            message = f"""{header}
{session_line}
{maintain}
    —————————————
"""
            
            for pred in self.session_predictions:
                message += f"{pred}\n"
            
            show_links = channel_config['show_links']
            show_promo = channel_config['show_promo']
            
            footer_content = ""
            
            if show_links:
                link_emoji = self.get_emoji('link', for_channel)
                footer_content += f"\n    {link_emoji} 𝐑𝐞𝐠𝐢𝐬𝐭𝐞𝐫 𝐋𝐢𝐧𝐤: \n    {channel_config['register_link']}\n    \n"
            
            if (show_links and show_promo) or (show_links and show_promo):
                footer_content += "    —————————————\n    \n"
            elif show_links and not show_promo:
                footer_content += "    —————————————"
            
            if show_promo:
                promo_text = self.format_promo_text_with_emojis(channel_config['promotional_text'], for_channel)
                footer_content += f"    {promo_text}\n    \n"
            
            if footer_content.strip():
                if not footer_content.strip().endswith("—————————————"):
                    footer_content += "    —————————————"
            
            if footer_template.strip() and footer_template != self.default_templates['prediction_footer']:
                try:
                    register_section = ""
                    if show_links:
                        register_section = f"\n    {self.get_emoji('link', for_channel)} 𝐑𝐞𝐠𝐢𝐬𝐭𝐞𝐫 𝐋𝐢𝐧𝐤: \n    {channel_config['register_link']}\n    \n    —————————————\n    \n"
                    
                    promo_section = ""
                    if show_promo:
                        promo_section = f"    {self.format_promo_text_with_emojis(channel_config['promotional_text'], for_channel)}\n    \n    —————————————"
                    
                    formatted_footer = register_section + promo_section
                    message += formatted_footer
                except KeyError as e:
                    logging.warning(f"⚠️ KeyError in footer template: {e}")
                    message += footer_content
            else:
                message += footer_content
            
            if not message or not message.strip():
                logging.error("❌ Final message is empty!")
                return ""
            
            logging.info(f"✅ Message formatted for channel {channel_id} ({len(message)} chars)")
            return message
            
        except Exception as e:
            logging.error(f"❌ Error formatting message for channel {channel_id}: {e}")
            import traceback
            logging.error(traceback.format_exc())
            return ""

    def get_big_small(self, num):
        return 'SMALL' if num <= 4 else 'BIG'

    def get_color(self, num):
        if num == 0:
            return 'GREEN'
        elif num in [1, 3, 5, 7, 9]:
            return 'RED'
        else:
            return 'VIOLET'

    async def fetch_live_data(self):
        url = self.config['api_url']
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
            'Accept': '*/*',
            'Accept-Language': 'en-US,en;q=0.9',
            'Origin': 'https://draw.ar-lottery01.com',
            'Referer': 'https://draw.ar-lottery01.com/',
            'Accept-Encoding': 'gzip, deflate, br'
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(url, headers=headers, timeout=15) as response:
                    if response.status != 200:
                        logging.error(f"API returned status code: {response.status}")
                        return None
                    
                    content_type = response.headers.get('Content-Type', '').lower()
                    
                    if 'application/json' in content_type:
                        data = await response.json()
                    else:
                        text_content = await response.text()
                        try:
                            data = json.loads(text_content)
                        except json.JSONDecodeError:
                            logging.error("Failed to parse response")
                            return None
                    
                    if data.get('data') and data['data'].get('list'):
                        data_list = data['data']['list']
                        formatted_data = []
                        for item in data_list:
                            try:
                                number_str = str(item.get('number', '0'))
                                number_clean = ''.join(filter(str.isdigit, number_str))
                                number = int(number_clean[0]) if number_clean else 0
                                
                                formatted_item = {
                                    'issueNumber': item.get('issueNumber'),
                                    'number': number,
                                    'color': self.get_color(number),
                                    'big_small': self.get_big_small(number),
                                    'premium': item.get('premium', ''),
                                    'sum': item.get('sum', '')
                                }
                                formatted_data.append(formatted_item)
                            except Exception as e:
                                continue
                        
                        # Update history tracking for AI
                        for item in formatted_data[:20]:
                            self.pattern_memory.append({
                                'result': item['big_small'],
                                'number': item['number'],
                                'timestamp': datetime.now()
                            })
                            self.number_memory.append(item['number'])
                            self.recent_results.append(item['big_small'])
                            self.recent_numbers.append(item['number'])
                            self.big_small_history.append(item['big_small'])
                            self.number_distribution[item['number']] += 1
                            self.last_actual_results.append(item['big_small'])
                        
                        return formatted_data if formatted_data else None
                    return None
                    
        except Exception as e:
            logging.error(f"Error fetching data: {e}")
            return None

    def detect_winning_patterns(self, results, numbers):
        """Pattern detection for better wins"""
        patterns = {}
        
        if len(results) < 10:
            return patterns
        
        # Current streak analysis
        current_streak = 1
        current_type = results[0]
        for i in range(1, len(results)):
            if results[i] == current_type:
                current_streak += 1
            else:
                break
        patterns['current_streak'] = current_streak
        patterns['streak_type'] = current_type
        
        # Balance analysis
        last_20_results = results[:20]
        big_count_20 = last_20_results.count('BIG')
        small_count_20 = last_20_results.count('SMALL')
        
        patterns['big_20'] = big_count_20
        patterns['small_20'] = small_count_20
        patterns['imbalance_20'] = big_count_20 - small_count_20
        
        # Gap analysis
        gap_big = 0
        gap_small = 0
        for i, r in enumerate(results[:10]):
            if r == 'BIG':
                gap_big = i
                break
        else:
            gap_big = 10
        
        for i, r in enumerate(results[:10]):
            if r == 'SMALL':
                gap_small = i
                break
        else:
            gap_small = 10
            
        patterns['gap_big'] = gap_big
        patterns['gap_small'] = gap_small
        
        # Number pattern analysis
        if numbers and len(numbers) >= 15:
            recent_numbers = numbers[:15]
            big_nums = sum(1 for n in recent_numbers if n >= 5)
            small_nums = sum(1 for n in recent_numbers if n <= 4)
            patterns['big_nums_15'] = big_nums
            patterns['small_nums_15'] = small_nums
            patterns['number_imbalance'] = big_nums - small_nums
            
            # Hot/Cold number analysis
            number_counter = Counter(recent_numbers)
            hot_numbers = [num for num, count in number_counter.items() if count >= 2]
            cold_numbers = [num for num in range(10) if num not in recent_numbers[-5:]]
            
            patterns['hot_numbers'] = hot_numbers
            patterns['cold_numbers'] = cold_numbers
            patterns['hot_big'] = sum(1 for n in hot_numbers if n >= 5)
            patterns['hot_small'] = sum(1 for n in hot_numbers if n <= 4)
            
            # Recent number trend
            recent_5 = numbers[:5]
            recent_trend_big = sum(1 for n in recent_5 if n >= 5)
            recent_trend_small = sum(1 for n in recent_5 if n <= 4)
            patterns['recent_trend'] = 'BIG' if recent_trend_big > recent_trend_small else 'SMALL'
        
        # Alternating pattern
        alternating_score = 0
        for i in range(2, min(10, len(results))):
            if results[i] != results[i-1]:
                alternating_score += 1
        patterns['alternating_score'] = alternating_score / 8.0
        
        # Check for consecutive same results
        consecutive_same = 0
        last_result = results[0]
        for result in results[:8]:
            if result == last_result:
                consecutive_same += 1
            else:
                break
        patterns['consecutive_same'] = consecutive_same
        
        return patterns

    def calculate_winning_strategies(self, patterns):
        """Calculate multiple winning strategies with better logic"""
        strategies = []
        
        # Strategy 1: Streak breaker (but with limit)
        if patterns.get('current_streak', 0) >= 2:
            if patterns['current_streak'] >= 3:
                prediction = 'BIG' if patterns['streak_type'] == 'SMALL' else 'SMALL'
                confidence = min(90, 70 + (patterns['current_streak'] - 2) * 10)
                strategies.append(('streak_breaker_long', prediction, confidence))
            elif patterns['current_streak'] == 2:
                if random.random() < 0.4:
                    prediction = patterns['streak_type']
                    confidence = 65
                    strategies.append(('streak_continue', prediction, confidence))
                else:
                    prediction = 'BIG' if patterns['streak_type'] == 'SMALL' else 'SMALL'
                    confidence = 70
                    strategies.append(('streak_breaker_short', prediction, confidence))
        
        # Strategy 2: Balance correction
        imbalance = patterns.get('imbalance_20', 0)
        if abs(imbalance) >= 3:
            if imbalance > 0:
                prediction = 'SMALL'
                confidence = min(85, 70 + abs(imbalance) * 3)
            else:
                prediction = 'BIG'
                confidence = min(85, 70 + abs(imbalance) * 3)
            strategies.append(('balance_correction', prediction, confidence))
        
        # Strategy 3: Gap filling
        gap_diff = patterns.get('gap_big', 0) - patterns.get('gap_small', 0)
        if abs(gap_diff) >= 3:
            if gap_diff > 0:
                prediction = 'BIG'
                confidence = 75 + min(15, gap_diff * 3)
            else:
                prediction = 'SMALL'
                confidence = 75 + min(15, abs(gap_diff) * 3)
            strategies.append(('gap_filling', prediction, confidence))
        
        # Strategy 4: Number pattern
        number_imbalance = patterns.get('number_imbalance', 0)
        if abs(number_imbalance) >= 4:
            if number_imbalance > 0:
                prediction = 'SMALL'
                confidence = 70 + min(20, number_imbalance * 2)
            else:
                prediction = 'BIG'
                confidence = 70 + min(20, abs(number_imbalance) * 2)
            strategies.append(('number_pattern_correction', prediction, confidence))
        
        # Strategy 5: Recent trend
        if 'recent_trend' in patterns:
            recent_trend = patterns['recent_trend']
            if patterns.get('consecutive_same', 0) < 3:
                prediction = recent_trend
                confidence = 65
                strategies.append(('trend_following', prediction, confidence))
        
        # Strategy 6: Random walk
        if random.random() < 0.2:
            prediction = random.choice(['BIG', 'SMALL'])
            confidence = 55
            strategies.append(('random_walk', prediction, confidence))
        
        # Strategy 7: Hot number analysis
        if patterns.get('hot_big', 0) > patterns.get('hot_small', 0) + 2:
            prediction = 'BIG'
            confidence = 70
            strategies.append(('hot_number_big', prediction, confidence))
        elif patterns.get('hot_small', 0) > patterns.get('hot_big', 0) + 2:
            prediction = 'SMALL'
            confidence = 70
            strategies.append(('hot_number_small', prediction, confidence))
        
        # Strategy 8: Alternating pattern
        if patterns.get('alternating_score', 0) > 0.7:
            last_result = self.last_actual_results[0] if self.last_actual_results else None
            if last_result:
                prediction = 'BIG' if last_result == 'SMALL' else 'SMALL'
                confidence = 70
                strategies.append(('alternating_pattern', prediction, confidence))
        
        return strategies

    def combine_winning_strategies(self, strategies):
        """Combine strategies with safety limits"""
        if not strategies:
            return random.choice(['BIG', 'SMALL']), 50
        
        big_score = 0
        small_score = 0
        
        for strategy_name, prediction, confidence in strategies:
            weight = self.pattern_weights.get(strategy_name, 0.1)
            strategy_success = self.strategy_success_count.get(strategy_name, 0.5)
            adjusted_weight = weight * (0.5 + strategy_success)
            
            score = confidence * adjusted_weight
            
            if prediction == 'BIG':
                big_score += score
            else:
                small_score += score
        
        # Safety check
        if self.consecutive_losses >= 2:
            logging.info(f"🛡️ Safety mode active: {self.consecutive_losses} consecutive losses")
            if self.consecutive_losses >= 3:
                if big_score > small_score:
                    return 'SMALL', min(80, small_score + 20)
                else:
                    return 'BIG', min(80, big_score + 20)
        
        # Normal decision
        if big_score > small_score:
            final_confidence = min(95, big_score)
            return 'BIG', final_confidence
        else:
            final_confidence = min(95, small_score)
            return 'SMALL', final_confidence

    def analyze_pattern_advanced(self, data_list):
        """NEW: Use AI for pattern analysis"""
        return self.analyze_pattern_with_ai(data_list)

    def get_next_period(self, current_period):
        try:
            return str(int(current_period) + 1)
        except:
            import re
            numbers = re.findall(r'\d+', current_period)
            return str(int(numbers[-1]) + 1) if numbers else "000001"

    def get_current_session(self):
        utc_now = datetime.utcnow()
        ist_now = utc_now + timedelta(hours=5, minutes=30)
        
        current_hour = ist_now.hour
        current_minute = ist_now.minute
        
        if current_minute < 45:
            session_start_hour = current_hour
            session_start_minute = 0
            session_end_hour = current_hour
            session_end_minute = 45
            is_active_period = True
        else:
            session_start_hour = current_hour
            session_start_minute = 45
            session_end_hour = (current_hour + 1) % 24
            session_end_minute = 0
            is_active_period = False
        
        if is_active_period:
            next_start_hour = current_hour
            next_start_minute = 45
            next_end_hour = (current_hour + 1) % 24
            next_end_minute = 0
        else:
            next_start_hour = (current_hour + 1) % 24
            next_start_minute = 0
            next_end_hour = next_start_hour
            next_end_minute = 45
        
        start_hour_12 = session_start_hour % 12
        if start_hour_12 == 0:
            start_hour_12 = 12
        start_am_pm = "AM" if session_start_hour < 12 else "PM"
        
        end_hour_12 = session_end_hour % 12
        if end_hour_12 == 0:
            end_hour_12 = 12
        end_am_pm = "AM" if session_end_hour < 12 else "PM"
        
        if session_start_minute == 0:
            current_session = f"{start_hour_12}:00{start_am_pm}-{end_hour_12}:45{end_am_pm}"
        else:
            current_session = f"{start_hour_12}:45{start_am_pm}-{end_hour_12}:00{end_am_pm}"
        
        next_start_12 = next_start_hour % 12
        if next_start_12 == 0:
            next_start_12 = 12
        next_start_am_pm = "AM" if next_start_hour < 12 else "PM"
        
        next_end_12 = next_end_hour % 12
        if next_end_12 == 0:
            next_end_12 = 12
        next_end_am_pm = "AM" if next_end_hour < 12 else "PM"
        
        if next_start_minute == 0:
            next_session = f"{next_start_12}:00{next_start_am_pm}-{next_end_12}:45{next_end_am_pm}"
        else:
            next_session = f"{next_start_12}:45{next_start_am_pm}-{next_end_12}:00{next_end_am_pm}"
        
        return current_session, is_active_period, current_hour, current_minute, next_session

    def is_operational_time(self, current_hour, current_minute):
        if current_hour < self.operational_hours_start:
            return False
        elif current_hour > self.operational_hours_end:
            return False
        elif current_hour == self.operational_hours_end and current_minute >= 45:
            return False
        else:
            return True

    async def send_combined_message(self, context: ContextTypes.DEFAULT_TYPE, for_channel=False):
        """Send message to active channels with prediction status check"""
        if not self.active_channels:
            logging.warning(f"No active channels")
            return
        
        success_count = 0
        for channel in self.active_channels:
            try:
                if not self.is_channel_prediction_active(channel):
                    logging.info(f"⏸️ Predictions paused for channel {channel}")
                    continue
                
                use_premium = for_channel and self.use_user_account
                
                message_text = self.format_session_message(channel, for_channel=use_premium)
                
                if not message_text or not message_text.strip():
                    logging.error(f"❌ Message text is empty for channel {channel}")
                    continue
                
                result = await self.send_message_with_retry(
                    context=context,
                    chat_id=channel,
                    text=message_text,
                    for_channel=use_premium
                )
                
                if result:
                    success_count += 1
                    logging.info(f"✅ Message sent to {channel}")
                else:
                    logging.error(f"❌ Failed to send to {channel}")
                    
            except Exception as e:
                logging.error(f"❌ Error sending to {channel}: {e}")
        
        logging.info(f"📤 Messages sent: {success_count}/{len([c for c in self.active_channels if self.is_channel_prediction_active(c)])}")

    async def check_result_and_send_next(self, context: ContextTypes.DEFAULT_TYPE, data):
        """Send next prediction with AI learning"""
        if not self.current_prediction_period or not self.waiting_for_result:
            return False
        
        result_found = False
        for item in data[:10]:
            if item['issueNumber'] == self.current_prediction_period:
                result = item['big_small']
                is_win = self.current_prediction_choice == result
                
                period_short = self.current_prediction_period[-2:] if len(self.current_prediction_period) >= 2 else self.current_prediction_period
                
                for i, pred in enumerate(self.session_predictions):
                    if pred.startswith(period_short):
                        if is_win:
                            fire_emoji = self.get_emoji('fire', for_channel=True)
                            if self.current_prediction_choice == 'BIG':
                                self.session_predictions[i] = f"{period_short} BIGGG {fire_emoji}{fire_emoji}{fire_emoji}{fire_emoji}"
                            else:
                                self.session_predictions[i] = f"{period_short} SMALL {fire_emoji}{fire_emoji}{fire_emoji}{fire_emoji}"
                        else:
                            choice_text = "BIGGG" if self.current_prediction_choice == 'BIG' else "SMALL"
                            self.session_predictions[i] = f"{period_short} {choice_text}"
                        break
                
                # NEW: AI Learning from result
                results = [item['big_small'] for item in data[:20]]
                numbers = [item['number'] for item in data[:20]]
                
                # Calculate pattern hash for learning
                result_numeric = [1 if r == 'BIG' else 0 for r in results[:self.pattern_window_size]]
                if len(result_numeric) >= self.pattern_window_size:
                    pattern_hash = self.calculate_pattern_hash(result_numeric)
                    
                    # Learn from this pattern
                    self.learn_from_pattern(pattern_hash, self.current_prediction_choice, is_win)
                    
                    # Update AI statistics
                    self.ai_prediction_history.append({
                        'prediction': self.current_prediction_choice,
                        'result': result,
                        'was_correct': is_win,
                        'pattern_hash': pattern_hash,
                        'timestamp': datetime.now().isoformat()
                    })
                
                if is_win:
                    self.session_wins += 1
                    self.consecutive_wins += 1
                    self.consecutive_losses = 0
                    self.last_prediction_was_loss = False
                    self.last_result_was_win = True
                    logging.info(f"✅ WIN! {self.current_prediction_choice} == {result}")
                    
                    if hasattr(self, 'last_strategy'):
                        self.strategy_success_count[self.last_strategy] = self.strategy_success_count.get(self.last_strategy, 0) + 1
                else:
                    self.session_losses += 1
                    self.consecutive_losses += 1
                    self.consecutive_wins = 0
                    self.last_prediction_was_loss = True
                    self.last_result_was_win = False
                    logging.info(f"❌ LOSS! {self.current_prediction_choice} != {result}")
                    
                    if hasattr(self, 'last_strategy'):
                        self.strategy_success_count[self.last_strategy] = max(0, self.strategy_success_count.get(self.last_strategy, 0.5) - 0.1)
                
                result_found = True
                break
        
        if result_found:
            latest = data[0]
            latest_period = latest.get('issueNumber')
            next_period = self.get_next_period(latest_period)
            
            # NEW: Use AI enhanced prediction
            choice, confidence = self.analyze_pattern_advanced(data)
            
            period_short = next_period[-2:] if len(next_period) >= 2 else next_period
            
            if choice == 'BIG':
                prediction_line = f"{period_short} BIGGG"
            else:
                prediction_line = f"{period_short} SMALL"
            
            self.session_predictions.append(prediction_line)
            
            self.current_prediction_period = next_period
            self.current_prediction_choice = choice
            self.waiting_for_result = True
            
            logging.info(f"🎯 Next prediction: {choice} (Confidence: {confidence:.1f}%)")
            logging.info(f"📊 Session stats: {self.session_wins}W {self.session_losses}L (Win rate: {(self.session_wins/(self.session_wins+self.session_losses)*100 if (self.session_wins+self.session_losses) > 0 else 0):.1f}%)")
            logging.info(f"🤖 AI Accuracy: {self.ai_accuracy:.2%}")
            
            await self.send_combined_message(context, for_channel=True)
            return True
        
        return False

    async def send_first_prediction(self, context: ContextTypes.DEFAULT_TYPE, data):
        """Send first prediction"""
        if self.waiting_for_result:
            return False
        
        latest = data[0]
        latest_period = latest.get('issueNumber')
        next_period = self.get_next_period(latest_period)
        
        # NEW: Use AI enhanced prediction
        choice, confidence = self.analyze_pattern_advanced(data)
        
        period_short = next_period[-2:] if len(next_period) >= 2 else next_period
        
        if choice == 'BIG':
            prediction_line = f"{period_short} BIGGG"
        else:
            prediction_line = f"{period_short} SMALL"
        
        self.session_predictions.append(prediction_line)
        
        self.current_prediction_period = next_period
        self.current_prediction_choice = choice
        self.waiting_for_result = True
        
        logging.info(f"🎯 First prediction: {choice} (Confidence: {confidence:.1f}%)")
        logging.info(f"🤖 AI Accuracy: {self.ai_accuracy:.2%}")
        logging.info(f"📊 Starting fresh session")
        
        await self.send_combined_message(context, for_channel=True)
        return True

    async def send_new_session_message(self, context: ContextTypes.DEFAULT_TYPE):
        """Send new session message"""
        if not self.active_channels:
            return
            
        success_count = 0
        for channel in self.active_channels:
            try:
                if not self.is_channel_prediction_active(channel):
                    continue
                    
                channel_config = self.get_channel_config(channel)
                
                show_links = channel_config['show_links']
                show_promo = channel_config['show_promo']
                
                message_text = self.get_channel_template(channel, 'new_session')
                formatted_text = self.format_with_emojis(message_text, for_channel=True)
                
                try:
                    register_link = channel_config['register_link'] if show_links else ""
                    
                    promo_text = channel_config['promotional_text']
                    if show_promo:
                        promo_text = self.format_promo_text_with_emojis(promo_text, for_channel=True)
                    else:
                        promo_text = ""
                    
                    formatted_text = formatted_text.format(
                        session=self.current_session,
                        register_link=register_link,
                        promo_text=promo_text
                    )
                except KeyError as e:
                    logging.warning(f"⚠️ KeyError in new session message for {channel}: {e}")
                    formatted_text = formatted_text.replace("{session}", self.current_session)
                    formatted_text = formatted_text.replace("{register_link}", register_link)
                    formatted_text = formatted_text.replace("{promo_text}", promo_text)
                
                if not formatted_text or not formatted_text.strip():
                    logging.error(f"❌ Session message is empty for channel {channel}")
                    continue
                
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel,
                    text=formatted_text,
                    for_channel=True
                )
                success_count += 1
                logging.info(f"✅ New session message sent to {channel}")
                
            except Exception as e:
                logging.error(f"❌ Failed to send new session message to {channel}: {e}")
        
        logging.info(f"✅ New session messages sent: {success_count}/{len(self.active_channels)}")

    async def send_good_morning_message(self, context: ContextTypes.DEFAULT_TYPE):
        """Send good morning message"""
        self.morning_message_sent = True
        self.night_message_sent = False
        
        self.session_ended = False
        self.in_break_period = False
        self.break_message_sent = False
        self.waiting_for_result = False
        self.last_result_was_win = False
        self.waiting_for_win = False
        
        self.session_predictions = []
        self.session_wins = 0
        self.session_losses = 0
        self.consecutive_losses = 0
        self.consecutive_wins = 0
        self.big_small_history.clear()
        
        if not self.active_channels:
            return
            
        success_count = 0
        for channel in self.active_channels:
            try:
                channel_config = self.get_channel_config(channel)
                
                show_links = channel_config['show_links']
                show_promo = channel_config['show_promo']
                
                message_text = self.get_channel_template(channel, 'good_morning')
                formatted_text = self.format_with_emojis(message_text, for_channel=True)
                
                try:
                    register_link = channel_config['register_link'] if show_links else ""
                    
                    promo_text = channel_config['promotional_text']
                    if show_promo:
                        promo_text = self.format_promo_text_with_emojis(promo_text, for_channel=True)
                    else:
                        promo_text = ""
                    
                    formatted_text = formatted_text.format(
                        register_link=register_link,
                        promo_text=promo_text
                    )
                except KeyError as e:
                    logging.warning(f"⚠️ KeyError in morning message for {channel}: {e}")
                    formatted_text = formatted_text.replace("{register_link}", register_link)
                    formatted_text = formatted_text.replace("{promo_text}", promo_text)
                
                if not formatted_text or not formatted_text.strip():
                    logging.error(f"❌ Morning message is empty for channel {channel}")
                    continue
                
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel,
                    text=formatted_text,
                    for_channel=True
                )
                success_count += 1
                logging.info(f"✅ Morning message sent to {channel}")
                
            except Exception as e:
                logging.error(f"❌ Failed to send morning message to {channel}: {e}")
        
        logging.info(f"✅ Morning messages sent: {success_count}/{len(self.active_channels)}")

    async def send_good_night_message(self, context: ContextTypes.DEFAULT_TYPE):
        """Send good night message"""
        self.night_message_sent = True
        self.morning_message_sent = False
        
        total_predictions = self.session_wins + self.session_losses
        win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0
        
        if not self.active_channels:
            return
            
        success_count = 0
        for channel in self.active_channels:
            try:
                channel_config = self.get_channel_config(channel)
                
                show_links = channel_config['show_links']
                show_promo = channel_config['show_promo']
                
                message_text = self.get_channel_template(channel, 'good_night')
                formatted_text = self.format_with_emojis(message_text, for_channel=True)
                
                try:
                    register_link = channel_config['register_link'] if show_links else ""
                    
                    promo_text = channel_config['promotional_text']
                    if show_promo:
                        promo_text = self.format_promo_text_with_emojis(promo_text, for_channel=True)
                    else:
                        promo_text = ""
                    
                    formatted_text = formatted_text.format(
                        wins=self.session_wins,
                        losses=self.session_losses,
                        win_rate=win_rate,
                        register_link=register_link,
                        promo_text=promo_text
                    )
                except KeyError as e:
                    logging.warning(f"⚠️ KeyError in night message for {channel}: {e}")
                    formatted_text = formatted_text.replace("{wins}", str(self.session_wins))
                    formatted_text = formatted_text.replace("{losses}", str(self.session_losses))
                    formatted_text = formatted_text.replace("{win_rate}", f"{win_rate:.1f}")
                    formatted_text = formatted_text.replace("{register_link}", register_link)
                    formatted_text = formatted_text.replace("{promo_text}", promo_text)
                
                if not formatted_text or not formatted_text.strip():
                    logging.error(f"❌ Night message is empty for channel {channel}")
                    continue
                
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel,
                    text=formatted_text,
                    for_channel=True
                )
                success_count += 1
                logging.info(f"✅ Night message sent to {channel}")
                
            except Exception as e:
                logging.error(f"❌ Failed to send night message to {channel}: {e}")
        
        logging.info(f"✅ Night messages sent: {success_count}/{len(self.active_channels)}")

    async def send_break_message(self, context: ContextTypes.DEFAULT_TYPE, next_session):
        """Send break message"""
        logging.info(f"🔄 Sending break message for next session: {next_session}")
        
        await self.cancel_scheduled_tasks()
        
        self.sent_custom_messages_in_break = {}
        
        if not self.active_channels:
            return
            
        success_count = 0
        for channel in self.active_channels:
            try:
                channel_config = self.get_channel_config(channel)
                
                show_links = channel_config['show_links']
                show_promo = channel_config['show_promo']
                
                message_text = self.get_channel_template(channel, 'break_message')
                formatted_text = self.format_with_emojis(message_text, for_channel=True)
                
                try:
                    promo_text = channel_config['promotional_text']
                    if show_promo:
                        promo_text = self.format_promo_text_with_emojis(promo_text, for_channel=True)
                    else:
                        promo_text = ""
                    
                    register_link = channel_config['register_link'] if show_links else ""
                    
                    formatted_text = formatted_text.format(
                        next_session=next_session,
                        promo_text=promo_text,
                        register_link=register_link
                    )
                except KeyError as e:
                    logging.warning(f"Key error in break message for {channel}: {e}")
                    formatted_text = formatted_text.replace("{next_session}", next_session)
                    formatted_text = formatted_text.replace("{promo_text}", promo_text)
                    formatted_text = formatted_text.replace("{register_link}", register_link)
                
                if not formatted_text or not formatted_text.strip():
                    logging.error(f"❌ Break message is empty for channel {channel}")
                    continue
                
                result = await self.send_message_with_retry(
                    context=context,
                    chat_id=channel,
                    text=formatted_text,
                    for_channel=True
                )
                if result:
                    success_count += 1
                    logging.info(f"✅ Break message sent to {channel}")
                    
                    if channel_config.get('custom_break_enabled', False):
                        messages = self.get_custom_break_messages(channel)
                        if messages:
                            delay_minutes = channel_config.get('custom_break_delay', 5)
                            logging.info(f"⏰ Scheduling {len(messages)} custom break messages for {channel} in {delay_minutes} minutes")
                            
                            for message_index, message_data in enumerate(messages):
                                message_delay = (delay_minutes * 60) + (message_index * 60)
                                task = asyncio.create_task(
                                    self.send_custom_break_message_delayed(
                                        context, channel, message_index, message_delay
                                    )
                                )
                                
                                task_key = f"{channel}:{message_index}"
                                self.scheduled_tasks[task_key] = task
                                
                                logging.info(f"⏰ Scheduled message {message_index+1} for {channel} with {message_delay} seconds delay")
                else:
                    logging.error(f"❌ Failed to send break message to {channel}")
                    
            except Exception as e:
                logging.error(f"❌ Exception sending break message to {channel}: {e}")
        
        logging.info(f"✅ Break messages sent: {success_count}/{len(self.active_channels)}")

    async def cancel_scheduled_tasks(self):
        """Cancel all scheduled custom break message tasks"""
        try:
            for task_key, task in list(self.scheduled_tasks.items()):
                if not task.done():
                    task.cancel()
                    logging.info(f"❌ Cancelled scheduled task: {task_key}")
            self.scheduled_tasks.clear()
        except Exception as e:
            logging.error(f"❌ Error cancelling tasks: {e}")

    async def send_custom_break_message_delayed(self, context: ContextTypes.DEFAULT_TYPE, channel_id, message_index, delay_seconds):
        """Send custom break message after delay"""
        try:
            logging.info(f"⏰ Waiting {delay_seconds} seconds before sending custom break message {message_index+1} to {channel_id}")
            await asyncio.sleep(delay_seconds)
            
            if not self.is_channel_prediction_active(channel_id):
                logging.info(f"⏸️ Channel {channel_id} predictions paused, skipping custom message")
                return
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                logging.warning(f"⚠️ No custom break message found for {channel_id} at index {message_index}")
                return
            
            await self.send_custom_break_message(context, channel_id, message_data, message_index)
            
        except asyncio.CancelledError:
            logging.info(f"⏹️ Custom break message {message_index+1} for {channel_id} cancelled")
        except Exception as e:
            logging.error(f"❌ Error in delayed custom break message for {channel_id}: {e}")

    async def send_custom_break_message(self, context: ContextTypes.DEFAULT_TYPE, channel_id, message_data, message_index=0):
        """Send custom break message"""
        try:
            logging.info(f"🎨 Sending custom break message {message_index+1} to {channel_id}")
            
            media_items = message_data.get('media_items', [])
            text_content = message_data.get('text_content', '')
            
            use_user_account = self.use_user_account
            
            if text_content:
                text_content = self.format_custom_message_with_premium_emojis(text_content, channel_id)
                logging.info(f"✅ Formatted text: {text_content[:100]}...")
            
            if media_items:
                logging.info(f"📸 Sending {len(media_items)} media items with custom break message {message_index+1}")
                
                formatted_media_group = []
                for i, media_item in enumerate(media_items):
                    item_type = media_item.get('type', 'photo')
                    item_media = media_item.get('file_id')
                    
                    final_caption = text_content if i == 0 else None
                    
                    formatted_media_group.append({
                        'type': item_type,
                        'media': item_media,
                        'caption': final_caption
                    })
                
                result = await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    for_channel=use_user_account,
                    media_group=formatted_media_group
                )
                
                if result:
                    logging.info(f"✅ Custom break message {message_index+1} with {len(media_items)} media items sent to {channel_id}")
                else:
                    logging.error(f"❌ Failed to send custom break message {message_index+1} to {channel_id}")
                
            elif text_content:
                result = await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    text=text_content,
                    for_channel=use_user_account
                )
                
                if result:
                    logging.info(f"✅ Custom text break message {message_index+1} sent to {channel_id}")
                else:
                    logging.error(f"❌ Failed to send custom text break message {message_index+1} to {channel_id}")
                    
            else:
                logging.warning(f"⚠️ No content found for custom break message {message_index+1} to {channel_id}")
                
        except Exception as e:
            logging.error(f"❌ Error sending custom break message {message_index+1} to {channel_id}: {e}")

    def get_keyboard(self, keyboard_type, channel_id=None, message_index=None):
        """Get keyboard with NEW: AI Statistics display"""
        
        # Main menu - with AI statistics
        main_menu = [
            [InlineKeyboardButton("📊 Stats & AI", callback_data="stats")],
            [InlineKeyboardButton("⚙️ Channel Settings", callback_data="select_channel_config")],
            [InlineKeyboardButton("⏯️ Prediction Control", callback_data="prediction_control")],
            [InlineKeyboardButton("➕ Add Channel", callback_data="add_channel")],
            [InlineKeyboardButton("🗑️ Remove Channel", callback_data="remove_channel")],
            [InlineKeyboardButton("🎨 Multiple Break Msgs", callback_data="custom_break_menu")],
            [InlineKeyboardButton("🤖 AI Management", callback_data="ai_management")],
            [InlineKeyboardButton("🔄 Advanced", callback_data="advanced")]
        ]
        
        # NEW: AI Management Menu
        if keyboard_type == 'ai_management':
            ai_menu = [
                [InlineKeyboardButton("📈 AI Statistics", callback_data="ai_stats")],
                [InlineKeyboardButton("🔍 View Patterns", callback_data="view_patterns")],
                [InlineKeyboardButton("🔄 Retrain AI", callback_data="retrain_ai")],
                [InlineKeyboardButton("🧹 Clear AI Data", callback_data="clear_ai_data")],
                [InlineKeyboardButton("🎯 Pattern Analysis", callback_data="pattern_analysis")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(ai_menu)
        
        # Prediction control menu
        if keyboard_type == 'prediction_control':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            
            buttons = []
            for channel in self.active_channels:
                status = self.is_channel_prediction_active(channel)
                status_text = "🟢 Active" if status else "⏸️ Paused"
                buttons.append([InlineKeyboardButton(f"{status_text} {channel}", callback_data=f"toggle_channel_prediction:{channel}")])
            buttons.append([InlineKeyboardButton("🟢 Start All", callback_data="start_all_predictions")])
            buttons.append([InlineKeyboardButton("⏸️ Pause All", callback_data="pause_all_predictions")])
            buttons.append([InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        # Channel configuration menu
        if keyboard_type == 'channel_config' and channel_id:
            channel_status = self.is_channel_prediction_active(channel_id)
            status_text = "⏸️ Pause Predictions" if channel_status else "▶️ Start Predictions"
            
            channel_config_menu = [
                [InlineKeyboardButton(status_text, callback_data=f"toggle_single_channel_prediction:{channel_id}")],
                [InlineKeyboardButton("🔗 Links Setup", callback_data=f"links_setup:{channel_id}")],
                [InlineKeyboardButton("📝 Templates Setup", callback_data=f"templates_setup:{channel_id}")],
                [InlineKeyboardButton("🎨 Multiple Break Msgs", callback_data=f"custom_break_setup:{channel_id}")],
                [InlineKeyboardButton("👁️ View Config", callback_data=f"view_config:{channel_id}")],
                [InlineKeyboardButton("⚡ Toggle Features", callback_data=f"toggle_features:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(channel_config_menu)
        
        # Custom break menu
        elif keyboard_type == 'custom_break_menu':
            custom_break_menu = [
                [InlineKeyboardButton("📋 Manage by Channel", callback_data="select_channel_custom_break")],
                [InlineKeyboardButton("👁️ View All Messages", callback_data="view_all_custom_break")],
                [InlineKeyboardButton("🔄 Toggle Mode", callback_data="toggle_break_mode")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(custom_break_menu)
        
        # Custom break setup menu
        elif keyboard_type == 'custom_break_setup' and channel_id:
            channel_config = self.get_channel_config(channel_id)
            custom_break_status = "✅ Enabled" if channel_config.get('custom_break_enabled', False) else "❌ Disabled"
            messages = self.get_custom_break_messages(channel_id)
            message_count = len(messages)
            mode_text = "🔄 Sequential" if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else "🎲 Random"
            
            custom_break_setup_menu = [
                [InlineKeyboardButton(f"🔄 {custom_break_status} Custom Break", callback_data=f"toggle_custom_break:{channel_id}")],
                [InlineKeyboardButton(f"📊 Messages: {message_count}", callback_data=f"view_all_messages:{channel_id}")],
                [InlineKeyboardButton("➕ Add New Message", callback_data=f"add_custom_break:{channel_id}")],
                [InlineKeyboardButton("✏️ Edit Message", callback_data=f"select_message_edit:{channel_id}")],
                [InlineKeyboardButton("🗑️ Delete Message", callback_data=f"select_message_delete:{channel_id}")],
                [InlineKeyboardButton(f"🎲 Mode: {mode_text}", callback_data=f"toggle_break_mode:{channel_id}")],
                [InlineKeyboardButton("⏰ Set Delay", callback_data=f"set_break_delay:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(custom_break_setup_menu)
        
        # Select message to edit
        elif keyboard_type == 'select_message_edit' and channel_id:
            messages = self.get_custom_break_messages(channel_id)
            buttons = []
            for i, msg in enumerate(messages):
                media_count = len(msg.get('media_items', []))
                text_len = len(msg.get('text_content', ''))
                buttons.append([InlineKeyboardButton(f"📝 Msg {i+1}: {media_count} media, {text_len} chars", callback_data=f"edit_message:{channel_id}:{i}")])
            buttons.append([InlineKeyboardButton("➕ Add New", callback_data=f"add_custom_break:{channel_id}")])
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"custom_break_setup:{channel_id}")])
            return InlineKeyboardMarkup(buttons)
        
        # Select message to delete
        elif keyboard_type == 'select_message_delete' and channel_id:
            messages = self.get_custom_break_messages(channel_id)
            buttons = []
            for i, msg in enumerate(messages):
                media_count = len(msg.get('media_items', []))
                text_len = len(msg.get('text_content', ''))
                buttons.append([InlineKeyboardButton(f"🗑️ Delete Msg {i+1}", callback_data=f"delete_message_confirm:{channel_id}:{i}")])
            buttons.append([InlineKeyboardButton("🗑️ Delete ALL", callback_data=f"delete_all_messages:{channel_id}")])
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"custom_break_setup:{channel_id}")])
            return InlineKeyboardMarkup(buttons)
        
        # Message editing menu
        elif keyboard_type == 'edit_message' and channel_id and message_index is not None:
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                return self.get_keyboard('custom_break_setup', channel_id)
            
            media_count = len(message_data.get('media_items', []))
            text_len = len(message_data.get('text_content', ''))
            
            edit_message_menu = [
                [InlineKeyboardButton(f"🖼️ Edit Media ({media_count} items)", callback_data=f"edit_message_media:{channel_id}:{message_index}")],
                [InlineKeyboardButton(f"📝 Edit Text ({text_len} chars)", callback_data=f"edit_message_text:{channel_id}:{message_index}")],
                [InlineKeyboardButton("👁️ Preview", callback_data=f"preview_message:{channel_id}:{message_index}")],
                [InlineKeyboardButton("🔙 Back to Messages", callback_data=f"select_message_edit:{channel_id}")]
            ]
            return InlineKeyboardMarkup(edit_message_menu)
        
        # Links setup menu
        elif keyboard_type == 'links_setup' and channel_id:
            links_menu = [
                [InlineKeyboardButton("✏️ Change Register Link", callback_data=f"change_register_link:{channel_id}")],
                [InlineKeyboardButton("📢 Change Promo Text", callback_data=f"change_promo_text:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(links_menu)
        
        # Templates setup menu
        elif keyboard_type == 'templates_setup' and channel_id:
            templates_menu = [
                [InlineKeyboardButton("📄 Prediction Template", callback_data=f"edit_prediction_template:{channel_id}")],
                [InlineKeyboardButton("🌅 Morning Template", callback_data=f"edit_morning_template:{channel_id}")],
                [InlineKeyboardButton("🌙 Night Template", callback_data=f"edit_night_template:{channel_id}")],
                [InlineKeyboardButton("⏸️ Break Template", callback_data=f"edit_break_template:{channel_id}")],
                [InlineKeyboardButton("👁️ View Templates", callback_data=f"view_templates:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(templates_menu)
        
        # Toggle features menu
        elif keyboard_type == 'toggle_features' and channel_id:
            channel_config = self.get_channel_config(channel_id)
            
            show_links_text = "✅ Show Links" if channel_config['show_links'] else "❌ Hide Links"
            show_promo_text = "✅ Show Promo" if channel_config['show_promo'] else "❌ Hide Promo"
            
            toggle_menu = [
                [InlineKeyboardButton(show_links_text, callback_data=f"toggle_links:{channel_id}")],
                [InlineKeyboardButton(show_promo_text, callback_data=f"toggle_promo:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(toggle_menu)
        
        # Advanced menu
        elif keyboard_type == 'advanced':
            advanced_menu = [
                [InlineKeyboardButton("🔄 Reset Session", callback_data="reset_table")],
                [InlineKeyboardButton("🔄 Restart Bot", callback_data="restart_bot")],
                [InlineKeyboardButton("🔍 Resolve Peers", callback_data="resolve_peers")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(advanced_menu)
        
        # Channel selection menu
        elif keyboard_type == 'select_channel':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            
            buttons = []
            for channel in self.active_channels:
                buttons.append([InlineKeyboardButton(f"📢 {channel}", callback_data=f"channel_config:{channel}")])
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        # Custom break channel selection
        elif keyboard_type == 'select_channel_custom_break':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="custom_break_menu")]])
            
            buttons = []
            for channel in self.active_channels:
                messages = self.get_custom_break_messages(channel)
                message_count = len(messages)
                status = "✅" if self.get_channel_config(channel).get('custom_break_enabled', False) else "❌"
                buttons.append([InlineKeyboardButton(f"{status} {channel} ({message_count} msgs)", callback_data=f"custom_break_setup:{channel}")])
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="custom_break_menu")])
            return InlineKeyboardMarkup(buttons)
        
        # Remove channel menu
        elif keyboard_type == 'remove_channel':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            
            buttons = []
            for i, channel in enumerate(self.active_channels, 1):
                buttons.append([InlineKeyboardButton(f"❌ {i}. {channel}", callback_data=f"remove_channel_confirm:{channel}")])
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        # Default main menu
        return InlineKeyboardMarkup(main_menu)

    async def start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_user.id not in self.config['admin_ids']:
            await update.message.reply_text("Access denied contact admin @aviii56")
            return
            
        await update.message.reply_text(
            "🤖 WinGo Bot Admin Panel\n\n"
            "🎯 REAL AI PATTERN RECOGNITION\n"
            "• GPT-4/Claude like pattern learning\n"
            "• Win Rate: 80-85%+ target\n"
            "• Learns from every result\n\n"
            "🎨 Multiple Custom Break Messages\n"
            "⏯️ Per-Channel Prediction Control\n"
            "📎 Supports ANY file type\n\n"
            "Select an option below:",
            reply_markup=self.get_keyboard('main')
        )

    async def handle_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query
        await query.answer()
        
        if query.from_user.id not in self.config['admin_ids']:
            await query.edit_message_text("Not authorized")
            return
            
        data = query.data
        chat_id = query.message.chat_id
        
        try:
            if data == 'main_menu':
                await query.edit_message_text(
                    "🤖 WinGo Bot Admin Panel\n\n"
                    "🎯 REAL AI PATTERN RECOGNITION\n"
                    "• GPT-4/Claude like pattern learning\n"
                    "• Win Rate: 80-85%+ target\n"
                    "• Learns from every result\n\n"
                    "🎨 Multiple Custom Break Messages\n"
                    "⏯️ Per-Channel Prediction Control\n"
                    "📎 Supports ANY file type\n\n"
                    "Select an option below:",
                    reply_markup=self.get_keyboard('main')
                )
                
            elif data == 'stats':
                data_fetch = await self.fetch_live_data()
                if data_fetch and self.waiting_for_result:
                    await self.check_result_and_send_next(context, data_fetch)
                
                total_predictions = self.session_wins + self.session_losses
                session_win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0
                
                current_session, is_active_period, current_hour, current_minute, next_session = self.get_current_session()
                is_operational = self.is_operational_time(current_hour, current_minute)
                
                # Count active channels
                active_channels = [c for c in self.active_channels if self.is_channel_prediction_active(c)]
                paused_channels = [c for c in self.active_channels if not self.is_channel_prediction_active(c)]
                
                total_custom_messages = sum(len(msgs) for msgs in self.custom_break_messages.values() if isinstance(msgs, list))
                
                stats_text = f"""📊 Bot Statistics & AI Analysis

🤖 AI SYSTEM:
• AI Accuracy: {self.ai_accuracy:.2%}
• AI Predictions: {self.ai_total_predictions}
• AI Correct: {self.ai_correct_predictions}
• Learning Cycles: {self.ai_learning_cycles}
• Patterns Learned: {len(self.pattern_database)}

📈 PERFORMANCE:
• Session: {self.session_wins}W {self.session_losses}L
• Win Rate: {session_win_rate:.1f}%
• Consecutive Wins: {self.consecutive_wins}
• Consecutive Losses: {self.consecutive_losses}
• Last Result: {'🟢 WIN' if self.last_result_was_win else '🔴 LOSS'}

🌐 CHANNELS:
• Total Channels: {len(self.active_channels)}
• Active Predictions: {len(active_channels)}
• Paused Predictions: {len(paused_channels)}
• Custom Break Msgs: {total_custom_messages}

🕒 SYSTEM:
• Session: {current_session}
• Time: {current_hour:02d}:{current_minute:02d}
• Status: {'🟢 ACTIVE' if is_operational else '🔴 SLEEP'}
• User Account: {'🟢 Active' if self.use_user_account and self.user_app else '🔴 Inactive'}
• AI Status: {'🟢 Learning' if self.ai_total_predictions > 0 else '🟡 Training'}"""
                
                await query.edit_message_text(stats_text, reply_markup=self.get_keyboard('main'))
                
            # NEW: AI Management
            elif data == 'ai_management':
                await query.edit_message_text(
                    "🤖 AI Pattern Recognition Management\n\n"
                    "🎯 REAL AI Learning System\n"
                    "• Learns from every prediction\n"
                    "• Identifies winning patterns\n"
                    "• Improves accuracy over time\n\n"
                    "Current AI Accuracy: {:.2%}\n"
                    "Patterns Learned: {}\n\n"
                    "Select an option:".format(self.ai_accuracy, len(self.pattern_database)),
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'ai_stats':
                stats_text = f"""🤖 AI PATTERN RECOGNITION STATISTICS

📊 ACCURACY:
• Overall Accuracy: {self.ai_accuracy:.2%}
• Total Predictions: {self.ai_total_predictions}
• Correct Predictions: {self.ai_correct_predictions}
• Learning Cycles: {self.ai_learning_cycles}

🧠 PATTERN DATABASE:
• Patterns Learned: {len(self.pattern_database)}
• Pattern Types: {len(set(self.pattern_types.values()))}
• Recent Patterns: {len(self.recent_patterns)}

📈 PERFORMANCE TRENDS:
• Current Confidence: {getattr(self, 'last_ai_confidence', 0)*100:.1f}%
• Recent Success Rate: {(sum(1 for h in self.ai_prediction_history[-20:] if h.get('was_correct'))/20*100 if len(self.ai_prediction_history) >= 20 else 0):.1f}%
• Best Pattern Success: {max((p.get('success_rate', 0) for p in self.pattern_database.values()), default=0)*100:.1f}%

🔍 PATTERN ANALYSIS:
• Alternating Patterns: {self.pattern_types['alternating']}
• Streak Patterns: {self.pattern_types['streak']}
• Zigzag Patterns: {self.pattern_types['zigzag']}
• Cluster Patterns: {self.pattern_types['cluster']}"""
                
                await query.edit_message_text(stats_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'view_patterns':
                if not self.pattern_database:
                    await query.edit_message_text(
                        "❌ No patterns learned yet!\n\n"
                        "AI needs more data to learn patterns.",
                        reply_markup=self.get_keyboard('ai_management')
                    )
                    return
                
                patterns_text = "🔍 TOP WINNING PATTERNS:\n\n"
                
                # Get top 10 patterns by success rate
                sorted_patterns = sorted(
                    self.pattern_database.items(),
                    key=lambda x: x[1].get('success_rate', 0),
                    reverse=True
                )[:10]
                
                for i, (pattern_hash, pattern_data) in enumerate(sorted_patterns):
                    success_rate = pattern_data.get('success_rate', 0) * 100
                    occurrences = pattern_data.get('total_occurrences', 0)
                    last_seen = pattern_data.get('last_seen', 'Never')
                    
                    patterns_text += f"{i+1}. Success: {success_rate:.1f}% ({occurrences} times)\n"
                    patterns_text += f"   Last Seen: {last_seen[:16]}\n"
                    patterns_text += f"   Hash: {pattern_hash[:8]}...\n\n"
                
                patterns_text += f"Total Patterns: {len(self.pattern_database)}"
                
                await query.edit_message_text(patterns_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'retrain_ai':
                await query.edit_message_text("🔄 Retraining AI model...")
                self.retrain_ai_model()
                await query.edit_message_text(
                    f"✅ AI Model retrained!\n"
                    f"Learning Cycle: {self.ai_learning_cycles}\n"
                    f"Accuracy: {self.ai_accuracy:.2%}",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'clear_ai_data':
                confirm_keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("✅ Yes, Clear All", callback_data="confirm_clear_ai_data")],
                    [InlineKeyboardButton("❌ No, Keep Data", callback_data="ai_management")]
                ])
                await query.edit_message_text(
                    "⚠️ WARNING: Clear ALL AI Learning Data?\n\n"
                    "This will reset:\n"
                    "• All learned patterns\n"
                    "• AI accuracy history\n"
                    "• Pattern database\n\n"
                    "This action cannot be undone!",
                    reply_markup=confirm_keyboard
                )
                
            elif data == 'confirm_clear_ai_data':
                self.pattern_database = {}
                self.ai_correct_predictions = 0
                self.ai_total_predictions = 0
                self.ai_accuracy = 0.0
                self.ai_learning_cycles = 0
                self.pattern_history = []
                self.ai_prediction_history.clear()
                
                self.save_ai_model()
                
                await query.edit_message_text(
                    "✅ All AI data cleared!\n"
                    "AI will start learning from scratch.",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'pattern_analysis':
                if not self.ai_prediction_history:
                    await query.edit_message_text(
                        "❌ No prediction history yet!\n"
                        "AI needs to make more predictions.",
                        reply_markup=self.get_keyboard('ai_management')
                    )
                    return
                
                recent_history = list(self.ai_prediction_history)[-20:]
                correct = sum(1 for h in recent_history if h.get('was_correct'))
                total = len(recent_history)
                recent_accuracy = (correct / total * 100) if total > 0 else 0
                
                # Pattern type analysis
                pattern_types_count = Counter()
                for pattern_data in self.pattern_database.values():
                    pattern_str = pattern_data.get('pattern', '')
                    if len(pattern_str) >= 10:
                        pattern_type = self.identify_pattern_type([int(c) for c in pattern_str[:10]])
                        pattern_types_count[pattern_type] += 1
                
                analysis_text = f"""🎯 PATTERN ANALYSIS

📊 RECENT PERFORMANCE (Last 20):
• Accuracy: {recent_accuracy:.1f}%
• Correct: {correct}/{total}
• Win Streak: {self.consecutive_wins}
• Loss Streak: {self.consecutive_losses}

🧩 PATTERN DISTRIBUTION:
• Alternating: {pattern_types_count['alternating']}
• Streak: {pattern_types_count['streak']}
• Zigzag: {pattern_types_count['zigzag']}
• Cluster: {pattern_types_count['cluster']}
• Cycle: {pattern_types_count['cycle']}
• Random: {pattern_types_count['random']}

⚡ PREDICTION CONFIDENCE:
• Current: {getattr(self, 'last_ai_confidence', 0)*100:.1f}%
• Threshold: {self.ai_confidence_threshold*100:.0f}%
• AI Weight: {self.pattern_weights['ai_pattern']*100:.0f}%

🔮 RECOMMENDATION:
• {'✅ AI is performing well' if recent_accuracy > 65 else '⚠️ AI needs more training'}
• {'✅ Confidence is high' if getattr(self, 'last_ai_confidence', 0) > 0.7 else '⚠️ Low confidence predictions'}"""
                
                await query.edit_message_text(analysis_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'prediction_control':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!\n\nPlease add a channel first.",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "⏯️ Prediction Control\n\n"
                    "Control predictions for each channel individually:\n"
                    "• 🟢 = Predictions Active\n"
                    "• ⏸️ = Predictions Paused\n\n"
                    "Select channel to toggle:",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data.startswith('toggle_channel_prediction:'):
                channel_id = data.split(':', 1)[1]
                new_status = self.toggle_channel_prediction(channel_id)
                status_text = "🟢 ACTIVATED" if new_status else "⏸️ PAUSED"
                
                await query.edit_message_text(
                    f"✅ Predictions {status_text} for {channel_id}",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data.startswith('toggle_single_channel_prediction:'):
                channel_id = data.split(':', 1)[1]
                new_status = self.toggle_channel_prediction(channel_id)
                status_text = "🟢 ACTIVATED" if new_status else "⏸️ PAUSED"
                
                await query.edit_message_text(
                    f"✅ Predictions {status_text} for {channel_id}",
                    reply_markup=self.get_keyboard('channel_config', channel_id)
                )
                
            elif data == 'start_all_predictions':
                for channel_id in self.active_channels:
                    self.set_channel_prediction_status(channel_id, True)
                
                await query.edit_message_text(
                    "✅ All channel predictions STARTED!",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data == 'pause_all_predictions':
                for channel_id in self.active_channels:
                    self.set_channel_prediction_status(channel_id, False)
                
                await query.edit_message_text(
                    "⏸️ All channel predictions PAUSED!",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data == 'select_channel_config':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!\n\nPlease add a channel first.",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "📢 Select a channel to configure:",
                    reply_markup=self.get_keyboard('select_channel')
                )
                
            elif data == 'custom_break_menu':
                await query.edit_message_text(
                    "🎨 Multiple Custom Break Messages\n\n"
                    "Manage multiple custom messages that will be sent after break messages.\n"
                    "You can set different messages for each channel!\n\n"
                    "🎯 REAL AI PATTERN RECOGNITION ACTIVE\n"
                    "• Learns from every result\n"
                    "• Win Rate: 80-85%+ target\n\n"
                    "Features:\n"
                    "• Add multiple messages per channel\n"
                    "• Each message can have media + text\n"
                    "• Supports ANY file type\n"
                    "• Sequential or random mode",
                    reply_markup=self.get_keyboard('custom_break_menu')
                )
                
            elif data == 'select_channel_custom_break':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!",
                        reply_markup=self.get_keyboard('custom_break_menu')
                    )
                    return
                    
                await query.edit_message_text(
                    "📢 Select a channel to configure multiple custom break messages:",
                    reply_markup=self.get_keyboard('select_channel_custom_break')
                )
                
            elif data == 'view_all_custom_break':
                if not self.custom_break_messages:
                    await query.edit_message_text(
                        "❌ No custom break messages set!",
                        reply_markup=self.get_keyboard('custom_break_menu')
                    )
                    return
                
                messages_text = "👁️ All Custom Break Messages:\n\n"
                total_messages = 0
                for channel_id, messages in self.custom_break_messages.items():
                    if isinstance(messages, dict):
                        messages = [messages]
                    elif not isinstance(messages, list):
                        messages = []
                    
                    message_count = len(messages)
                    total_messages += message_count
                    channel_status = "✅" if self.get_channel_config(channel_id).get('custom_break_enabled', False) else "❌"
                    messages_text += f"• {channel_status} {channel_id}: {message_count} messages\n"
                    
                    for i, msg in enumerate(messages):
                        media_count = len(msg.get('media_items', []))
                        text_len = len(msg.get('text_content', ''))
                        messages_text += f"  └ Msg {i+1}: {media_count} media, {text_len} chars\n"
                
                messages_text += f"\n📊 Total: {total_messages} messages"
                
                await query.edit_message_text(
                    messages_text,
                    reply_markup=self.get_keyboard('custom_break_menu')
                )
                
            elif data == 'toggle_break_mode':
                await query.edit_message_text(
                    "🔄 Toggle Break Message Mode\n\n"
                    "This affects all channels:\n"
                    "• Sequential: Send messages in order\n"
                    "• Random: Send random message each time\n\n"
                    "Note: You can also set mode per channel in channel settings.",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🔄 Sequential", callback_data="set_global_mode:sequential")],
                        [InlineKeyboardButton("🎲 Random", callback_data="set_global_mode:random")],
                        [InlineKeyboardButton("🔙 Back", callback_data="custom_break_menu")]
                    ])
                )
                
            elif data.startswith('set_global_mode:'):
                mode = data.split(':', 1)[1]
                for channel_id in self.active_channels:
                    channel_config = self.get_channel_config(channel_id)
                    channel_config['custom_break_mode'] = mode
                    self.update_channel_config(channel_id, channel_config)
                
                await query.edit_message_text(
                    f"✅ All channels set to {mode} mode!",
                    reply_markup=self.get_keyboard('custom_break_menu')
                )
                
            elif data.startswith('channel_config:'):
                channel_id = data.split(':', 1)[1]
                channel_status = self.is_channel_prediction_active(channel_id)
                status_text = "🟢 ACTIVE" if channel_status else "⏸️ PAUSED"
                
                config_text = f"""⚙️ Configuration for {channel_id}

🎯 AI STATUS: {'🟢 ACTIVE' if self.ai_total_predictions > 50 else '🟡 TRAINING'}
AI Accuracy: {self.ai_accuracy:.2%}

Prediction Status: {status_text}

Select what you want to configure:"""
                
                await query.edit_message_text(
                    config_text,
                    reply_markup=self.get_keyboard('channel_config', channel_id)
                )
                
            elif data.startswith('custom_break_setup:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                messages = self.get_custom_break_messages(channel_id)
                
                status_text = "✅ Enabled" if channel_config.get('custom_break_enabled', False) else "❌ Disabled"
                message_count = len(messages)
                mode_text = "🔄 Sequential" if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else "🎲 Random"
                delay = channel_config.get('custom_break_delay', 5)
                
                setup_text = f"""🎨 Multiple Custom Break Messages for {channel_id}

🎯 REAL AI PATTERN RECOGNITION ACTIVE
• AI Accuracy: {self.ai_accuracy:.2%}
• Patterns Learned: {len(self.pattern_database)}

Status: {status_text}
Mode: {mode_text}
Total Messages: {message_count}
Delay: {delay} minutes after break

Options:"""
                
                await query.edit_message_text(
                    setup_text,
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('toggle_custom_break:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                current_status = channel_config.get('custom_break_enabled', False)
                channel_config['custom_break_enabled'] = not current_status
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['custom_break_enabled'] else "disabled"
                await query.edit_message_text(
                    f"✅ Custom break messages {status} for {channel_id}",
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('view_all_messages:'):
                channel_id = data.split(':', 1)[1]
                messages = self.get_custom_break_messages(channel_id)
                
                if not messages:
                    await query.edit_message_text(
                        f"❌ No custom break messages set for {channel_id}",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                messages_text = f"📊 Custom Break Messages for {channel_id}\n\n"
                for i, msg in enumerate(messages):
                    media_count = len(msg.get('media_items', []))
                    text_content = msg.get('text_content', '')
                    text_len = len(text_content)
                    preview = text_content[:50] + "..." if len(text_content) > 50 else text_content
                    messages_text += f"📝 Message {i+1}:\n"
                    messages_text += f"• Media: {media_count} items\n"
                    messages_text += f"• Text: {text_len} chars\n"
                    messages_text += f"• Preview: {preview}\n\n"
                
                await query.edit_message_text(
                    messages_text,
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('add_custom_break:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_new_message_name:{channel_id}'
                
                await query.edit_message_text(
                    f"➕ Add New Custom Break Message for {channel_id}\n\n"
                    f"🎯 REAL AI PATTERN RECOGNITION ACTIVE\n"
                    f"• AI Accuracy: {self.ai_accuracy:.2%}\n\n"
                    f"Examples: 🔥 🚀 👑 ✨ 💰 🎯\n\n"
                    f"First, give this message a name (for easy identification):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_break_setup:{channel_id}")]])
                )
                
            elif data.startswith('edit_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if not message_data:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                message_name = message_data.get('name', f'Message {message_index+1}')
                media_count = len(message_data.get('media_items', []))
                text_len = len(message_data.get('text_content', ''))
                
                await query.edit_message_text(
                    f"✏️ Edit Message: {message_name}\n\n"
                    f"Media: {media_count} items\n"
                    f"Text: {text_len} characters\n\n"
                    f"🎯 AI Pattern Detection Active\n\n"
                    f"Select what to edit:",
                    reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                )
                
            elif data.startswith('edit_message_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                self.user_state[chat_id] = f'awaiting_edit_message_media:{channel_id}:{message_index}'
                
                await query.edit_message_text(
                    f"🖼️ Edit Media for Message {message_index+1}\n\n"
                    f"Send photos, videos, or ANY file type to replace current media.\n"
                    f"You can send multiple files.\n\n"
                    f"Current media will be replaced!\n\n"
                    f"Send files now (multiple allowed):",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("✅ Keep Current Media", callback_data=f"edit_message:{channel_id}:{message_index}")],
                        [InlineKeyboardButton("🗑️ Clear All Media", callback_data=f"clear_message_media:{channel_id}:{message_index}")],
                        [InlineKeyboardButton("🔙 Cancel", callback_data=f"edit_message:{channel_id}:{message_index}")]
                    ])
                )
                
            elif data.startswith('clear_message_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if message_data:
                    message_data['media_items'] = []
                    self.update_custom_break_message(channel_id, message_index, message_data)
                    await query.edit_message_text(
                        f"✅ All media cleared from message {message_index+1}",
                        reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('edit_message_text:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                self.user_state[chat_id] = f'awaiting_edit_message_text:{channel_id}:{message_index}'
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                current_text = message_data.get('text_content', '') if message_data else ''
                
                await query.edit_message_text(
                    f"📝 Edit Text for Message {message_index+1}\n\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"Example: '🔥 HOT PREDICTIONS! 🚀 WIN BIG! 👑'\n\n"
                    f"Current text: {current_text[:100]}{'...' if len(current_text) > 100 else ''}\n\n"
                    f"Send the new text message:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"edit_message:{channel_id}:{message_index}")]])
                )
                
            elif data.startswith('preview_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if not message_data:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                message_name = message_data.get('name', f'Message {message_index+1}')
                media_count = len(message_data.get('media_items', []))
                text_content = message_data.get('text_content', '')
                text_len = len(text_content)
                
                preview_text = f"""👁️ Preview Message {message_index+1}: {message_name}

• Media Items: {media_count}
• Text Length: {text_len} characters

Text Preview (with premium emojis):
{self.format_custom_message_with_premium_emojis(text_content, channel_id)[:200]}{'...' if len(text_content) > 200 else ''}

Would you like to test send this message?"""
                
                await query.edit_message_text(
                    preview_text,
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🚀 Test Send", callback_data=f"test_send_message:{channel_id}:{message_index}")],
                        [InlineKeyboardButton("🔙 Back", callback_data=f"edit_message:{channel_id}:{message_index}")]
                    ])
                )
                
            elif data.startswith('test_send_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if message_data:
                    await query.edit_message_text("🚀 Sending test message...")
                    await self.send_custom_break_message(context, channel_id, message_data, message_index)
                    await query.edit_message_text(
                        f"✅ Test message sent to {channel_id}!\n"
                        f"🎯 Premium emojis were used if available.",
                        reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('select_message_edit:'):
                channel_id = data.split(':', 1)[1]
                messages = self.get_custom_break_messages(channel_id)
                
                if not messages:
                    await query.edit_message_text(
                        f"❌ No messages to edit!\n\nAdd a message first.",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                await query.edit_message_text(
                    f"✏️ Select Message to Edit for {channel_id}",
                    reply_markup=self.get_keyboard('select_message_edit', channel_id)
                )
                
            elif data.startswith('select_message_delete:'):
                channel_id = data.split(':', 1)[1]
                messages = self.get_custom_break_messages(channel_id)
                
                if not messages:
                    await query.edit_message_text(
                        f"❌ No messages to delete!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                await query.edit_message_text(
                    f"🗑️ Delete Message for {channel_id}\n\n"
                    f"Select which message to delete:",
                    reply_markup=self.get_keyboard('select_message_delete', channel_id)
                )
                
            elif data.startswith('delete_message_confirm:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                if self.delete_custom_break_message(channel_id, message_index):
                    await query.edit_message_text(
                        f"✅ Message {message_index+1} deleted for {channel_id}",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete message!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('delete_all_messages:'):
                channel_id = data.split(':', 1)[1]
                
                if self.delete_custom_break_message(channel_id):
                    await query.edit_message_text(
                        f"✅ ALL messages deleted for {channel_id}",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ No messages to delete!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('toggle_break_mode:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                current_mode = channel_config.get('custom_break_mode', 'sequential')
                new_mode = 'random' if current_mode == 'sequential' else 'sequential'
                channel_config['custom_break_mode'] = new_mode
                self.update_channel_config(channel_id, channel_config)
                
                mode_text = "Sequential" if new_mode == 'sequential' else "Random"
                await query.edit_message_text(
                    f"✅ Break message mode set to {mode_text} for {channel_id}",
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('set_break_delay:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_break_delay:{channel_id}'
                
                current_delay = self.get_channel_config(channel_id).get('custom_break_delay', 5)
                
                await query.edit_message_text(
                    f"⏰ Set Custom Break Message Delay for {channel_id}\n\n"
                    f"Current delay: {current_delay} minutes\n\n"
                    f"Enter the delay in minutes (1-60) after break message when the custom messages should be sent:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_break_setup:{channel_id}")]])
                )
                
            elif data.startswith('links_setup:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                links_text = f"""🔗 Links Setup for {channel_id}

🎯 AI STATUS: Accuracy {self.ai_accuracy:.2%}

Current Configuration:
• Register Link: {channel_config['register_link']}
• Promo Text: {channel_config['promotional_text'][:50]}...

Select what to change:"""
                
                await query.edit_message_text(
                    links_text,
                    reply_markup=self.get_keyboard('links_setup', channel_id)
                )
                
            elif data.startswith('templates_setup:'):
                channel_id = data.split(':', 1)[1]
                
                templates_text = f"""📝 Templates Setup for {channel_id}

🎯 REAL AI PATTERN RECOGNITION ACTIVE
• AI Accuracy: {self.ai_accuracy:.2%}
• Patterns: {len(self.pattern_database)}

Example: '🔥 HOT PREDICTIONS' will auto-convert

Select which template to edit:"""
                
                await query.edit_message_text(
                    templates_text,
                    reply_markup=self.get_keyboard('templates_setup', channel_id)
                )
                
            elif data.startswith('toggle_links:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                channel_config['show_links'] = not channel_config['show_links']
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['show_links'] else "disabled"
                logging.info(f"✅ Links display {status} for {channel_id}")
                
                updated_config = self.get_channel_config(channel_id)
                
                show_links_text = "✅ Show Links" if updated_config['show_links'] else "❌ Hide Links"
                show_promo_text = "✅ Show Promo" if updated_config['show_promo'] else "❌ Hide Promo"
                
                toggle_menu = [
                    [InlineKeyboardButton(show_links_text, callback_data=f"toggle_links:{channel_id}")],
                    [InlineKeyboardButton(show_promo_text, callback_data=f"toggle_promo:{channel_id}")],
                    [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
                ]
                
                await query.edit_message_text(
                    f"✅ Links display {status} for {channel_id}",
                    reply_markup=InlineKeyboardMarkup(toggle_menu)
                )
                
            elif data.startswith('toggle_promo:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                channel_config['show_promo'] = not channel_config['show_promo']
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['show_promo'] else "disabled"
                logging.info(f"✅ Promo text display {status} for {channel_id}")
                
                updated_config = self.get_channel_config(channel_id)
                
                show_links_text = "✅ Show Links" if updated_config['show_links'] else "❌ Hide Links"
                show_promo_text = "✅ Show Promo" if updated_config['show_promo'] else "❌ Hide Promo"
                
                toggle_menu = [
                    [InlineKeyboardButton(show_links_text, callback_data=f"toggle_links:{channel_id}")],
                    [InlineKeyboardButton(show_promo_text, callback_data=f"toggle_promo:{channel_id}")],
                    [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
                ]
                
                await query.edit_message_text(
                    f"✅ Promo text display {status} for {channel_id}",
                    reply_markup=InlineKeyboardMarkup(toggle_menu)
                )
                
            elif data.startswith('toggle_features:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                channel_status = self.is_channel_prediction_active(channel_id)
                
                features_text = f"""⚡ Feature Toggles for {channel_id}

🎯 AI STATUS:
• Accuracy: {self.ai_accuracy:.2%}
• Predictions: {self.ai_total_predictions}
• Learning: {'🟢 Active' if self.ai_total_predictions > 50 else '🟡 Training'}

Current Status:
• Predictions: {'🟢 Active' if channel_status else '⏸️ Paused'}
• Show Links: {'✅ Enabled' if channel_config['show_links'] else '❌ Disabled'}
• Show Promo Text: {'✅ Enabled' if channel_config['show_promo'] else '❌ Disabled'}
• Custom Break: {'✅ Enabled' if channel_config.get('custom_break_enabled', False) else '❌ Disabled'}
• Break Mode: {'🔄 Sequential' if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else '🎲 Random'}
• Premium Emojis: {'✅ Auto Convert' if self.use_user_account else '🔴 Manual Only'}
• AI Pattern Detection: ✅ Enabled

Toggle features on/off:"""
                
                await query.edit_message_text(
                    features_text,
                    reply_markup=self.get_keyboard('toggle_features', channel_id)
                )
                
            elif data.startswith('view_config:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                messages = self.get_custom_break_messages(channel_id)
                channel_status = self.is_channel_prediction_active(channel_id)
                
                config_text = f"""👁️ Full Configuration for {channel_id}

🎯 AI SYSTEM:
• AI Accuracy: {self.ai_accuracy:.2%}
• AI Weight: {self.pattern_weights['ai_pattern']*100:.0f}%
• Patterns Learned: {len(self.pattern_database)}

Prediction Status: {'🟢 ACTIVE' if channel_status else '⏸️ PAUSED'}

Links:
• Register Link: {channel_config['register_link']}
• Promo Text: {channel_config['promotional_text']}

Features:
• Show Links: {'✅ Yes' if channel_config['show_links'] else '❌ No'}
• Show Promo: {'✅ Yes' if channel_config['show_promo'] else '❌ No'}
• Custom Break: {'✅ Enabled' if channel_config.get('custom_break_enabled', False) else '❌ Disabled'}
• Break Mode: {'🔄 Sequential' if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else '🎲 Random'}
• Break Delay: {channel_config.get('custom_break_delay', 5)} minutes
• Premium Emojis: {'✅ Auto Convert Enabled' if self.use_user_account else '❌ Manual Only'}
• AI Pattern Detection: ✅ Enabled

Custom Break Messages: {len(messages)} messages

Templates Preview:
• Prediction: {self.get_channel_template(channel_id, 'prediction_header')[:50]}...
• Morning: {self.get_channel_template(channel_id, 'good_morning')[:50]}...
• Night: {self.get_channel_template(channel_id, 'good_night')[:50]}...
• Break: {self.get_channel_template(channel_id, 'break_message')[:50]}..."""
                
                await query.edit_message_text(
                    config_text,
                    reply_markup=self.get_keyboard('channel_config', channel_id)
                )
                
            elif data.startswith('change_register_link:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_register_link:{channel_id}'
                
                channel_config = self.get_channel_config(channel_id)
                await query.edit_message_text(
                    f"✏️ Change Register Link for {channel_id}\n\n"
                    f"Current: {channel_config['register_link']}\n\n"
                    f"Please send the new register link:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"links_setup:{channel_id}")]])
                )
                
            elif data.startswith('change_promo_text:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_promo_text:{channel_id}'
                
                channel_config = self.get_channel_config(channel_id)
                await query.edit_message_text(
                    f"📢 Change Promo Text for {channel_id}\n\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"Example: '🎁 Register now and get DAILY FREE GIFT CODE! 🎁'\n\n"
                    f"Current: {channel_config['promotional_text']}\n\n"
                    f"Please send the new promotional text:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"links_setup:{channel_id}")]])
                )
                
            elif data.startswith('edit_prediction_template:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_prediction_template:{channel_id}'
                
                current_template = self.get_channel_template(channel_id, 'prediction_header')
                await query.edit_message_text(
                    f"📄 Edit Prediction Template for {channel_id}\n\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"Example: '👑 𝐁𝐃𝐆 𝐖𝐈𝐍 𝐖𝐈𝐍𝐆𝐎 𝐎𝐅𝐅𝐈𝐂𝐈𝐀𝐋 👑'\n\n"
                    f"Current template (first 200 chars):\n{current_template[:200]}...\n\n"
                    f"Please send the new prediction template:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"templates_setup:{channel_id}")]])
                )
                
            elif data.startswith('edit_morning_template:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_morning_template:{channel_id}'
                
                current_template = self.get_channel_template(channel_id, 'good_morning')
                await query.edit_message_text(
                    f"🌅 Edit Morning Template for {channel_id}\n\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"Example: '🌅 𝐆𝐎𝐎𝐃 𝐌𝐎𝐑𝐍𝐈𝐍𝐆 𝐖𝐈𝐍𝐍𝐄𝐑𝐒! 🌅'\n\n"
                    f"Current template (first 200 chars):\n{current_template[:200]}...\n\n"
                    f"Please send the new morning template:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"templates_setup:{channel_id}")]])
                )
                
            elif data.startswith('edit_night_template:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_night_template:{channel_id}'
                
                current_template = self.get_channel_template(channel_id, 'good_night')
                await query.edit_message_text(
                    f"🌙 Edit Night Template for {channel_id}\n\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"Example: '🌙 𝐆𝐎𝐎𝐃 𝐍𝐈𝐆𝐇𝐓 𝐖𝐈𝐍𝐍𝐄𝐑𝐒! 🌙'\n\n"
                    f"Current template (first 200 chars):\n{current_template[:200]}...\n\n"
                    f"Please send the new night template:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"templates_setup:{channel_id}")]])
                )
                
            elif data.startswith('edit_break_template:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_break_template:{channel_id}'
                
                current_template = self.get_channel_template(channel_id, 'break_message')
                await query.edit_message_text(
                    f"⏸️ Edit Break Template for {channel_id}\n\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"Example: '⏸️ 𝐁𝐑𝐄𝐀𝐊 𝐓𝐈𝐌𝐄 ⏸️'\n\n"
                    f"Current template (first 200 chars):\n{current_template[:200]}...\n\n"
                    f"Please send the new break template:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"templates_setup:{channel_id}")]])
                )
                
            elif data.startswith('view_templates:'):
                channel_id = data.split(':', 1)[1]
                
                templates_text = f"""👁️ Templates for {channel_id}

Prediction Template:
{self.get_channel_template(channel_id, 'prediction_header')[:100]}...

Morning Template:
{self.get_channel_template(channel_id, 'good_morning')[:100]}...

Night Template:
{self.get_channel_template(channel_id, 'good_night')[:100]}...

Break Template:
{self.get_channel_template(channel_id, 'break_message')[:100]}...

Use the templates menu to edit any of these."""
                
                await query.edit_message_text(
                    templates_text,
                    reply_markup=self.get_keyboard('templates_setup', channel_id)
                )
                
            elif data == 'add_channel':
                self.user_state[chat_id] = 'awaiting_add_channel'
                await query.edit_message_text(
                    "➕ Add New Channel\n\n"
                    "Send channel username (@mychannel) or numeric ID (-1001234567890):\n\n"
                    "For user account: Bot/User must be member",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="main_menu")]])
                )
                
            elif data == 'remove_channel':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels to remove!",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "🗑️ Remove Channel\n\nSelect channel to remove:",
                    reply_markup=self.get_keyboard('remove_channel')
                )
                
            elif data.startswith('remove_channel_confirm:'):
                channel_id = data.split(':', 1)[1]
                if channel_id in self.active_channels:
                    self.active_channels.remove(channel_id)
                    if channel_id in self.channel_configs:
                        del self.channel_configs[channel_id]
                    if channel_id in self.channel_prediction_status:
                        del self.channel_prediction_status[channel_id]
                    if channel_id in self.resolved_peers:
                        del self.resolved_peers[channel_id]
                    if channel_id in self.failed_peers:
                        self.failed_peers.remove(channel_id)
                    if channel_id in self.custom_break_messages:
                        del self.custom_break_messages[channel_id]
                    if channel_id in self.custom_break_schedules:
                        del self.custom_break_schedules[channel_id]
                    self.save_config()
                    
                    await query.edit_message_text(
                        f"✅ Channel {channel_id} removed successfully!",
                        reply_markup=self.get_keyboard('main')
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Channel {channel_id} not found!",
                        reply_markup=self.get_keyboard('main')
                    )
                
            elif data == 'advanced':
                await query.edit_message_text(
                    "🔄 Advanced Options",
                    reply_markup=self.get_keyboard('advanced')
                )
                
            elif data == 'reset_table':
                self.session_predictions = []
                self.consecutive_losses = 0
                self.consecutive_wins = 0
                self.session_wins = 0
                self.session_losses = 0
                self.predictions = {}
                self.safety_mode = False
                self.recovery_mode = False
                self.ultra_safe_mode = False
                self.waiting_for_win = False
                self.session_ended = False
                self.last_prediction_was_loss = False
                self.in_break_period = False
                self.night_mode = False
                self.morning_message_sent = False
                self.night_message_sent = False
                self.last_sent_period = None
                self.last_prediction_time = None
                self.current_prediction_period = None
                self.current_prediction_choice = None
                self.waiting_for_result = False
                self.break_message_sent = False
                self.last_result_was_win = False
                self.big_small_history.clear()
                await query.edit_message_text(
                    "✅ Session reset complete!",
                    reply_markup=self.get_keyboard('advanced')
                )
                
            elif data == 'restart_bot':
                await query.edit_message_text("🔄 Restarting bot...")
                if self.user_app and self.use_user_account:
                    await self.user_app.stop()
                raise SystemExit(1)
                
            elif data == 'resolve_peers':
                if self.use_user_account and self.user_app:
                    await query.edit_message_text("🔍 Resolving peers...")
                    await self.resolve_all_channels()
                    await query.edit_message_text(
                        "✅ Peers resolved successfully!",
                        reply_markup=self.get_keyboard('advanced')
                    )
                else:
                    await query.edit_message_text(
                        "❌ User account not active",
                        reply_markup=self.get_keyboard('advanced')
                    )
                
        except Exception as e:
            logging.error(f"Callback error: {e}")
            import traceback
            logging.error(traceback.format_exc())
            await query.edit_message_text(
                f"❌ Error: {str(e)}",
                reply_markup=self.get_keyboard('main')
            )

    async def handle_message(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_user is None or update.effective_user.id not in self.config['admin_ids']:
            return
            
        chat_id = update.effective_chat.id
        message = update.message
        
        if chat_id not in self.user_state:
            return
            
        state = self.user_state[chat_id]
        text = message.text.strip() if message.text else ""
        
        # Add channel
        if state == 'awaiting_add_channel' and text:
            if text.startswith('@') or (text.lstrip('-').isdigit()):
                if text not in self.active_channels:
                    try:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=text,
                            text="🤖 Bot connectivity test"
                        )
                        
                        self.active_channels.append(text)
                        self.channel_prediction_status[text] = True
                        self.save_config()
                        
                        if self.use_user_account and self.user_app:
                            await self.resolve_all_channels()
                        
                        await message.reply_text(f"✅ Channel {text} added successfully!")
                        logging.info(f"✅ Channel added: {text}")
                        
                    except Exception as e:
                        await message.reply_text(f"❌ Cannot add channel: {str(e)}")
                        logging.error(f"❌ Failed to add channel: {e}")
                else:
                    await message.reply_text("❌ Channel already exists!")
            else:
                await message.reply_text("❌ Invalid format! Must start with @ or be numeric ID")
            del self.user_state[chat_id]
            
        # Handle message name for new custom break message
        elif state.startswith('awaiting_new_message_name:') and text:
            channel_id = state.split(':', 1)[1]
            message_name = text
            
            new_message = {
                'name': message_name,
                'media_items': [],
                'text_content': ''
            }
            
            message_index = self.add_custom_break_message(channel_id, new_message)
            
            self.user_state[chat_id] = f'awaiting_new_message_media:{channel_id}:{message_index}'
            
            await message.reply_text(
                f"✅ Message '{message_name}' created!\n\n"
                f"🎯 Now, send photos, videos, or ANY file type for this message.\n"
                f"🎯 AI Pattern Detection Active\n\n"
                f"You can send multiple files, or send /skip to skip adding media."
            )
            
        # Handle media for new message
        elif state.startswith('awaiting_new_message_media:') and (message.photo or message.video or message.document or message.animation or text == '/skip'):
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            
            if text == '/skip':
                self.user_state[chat_id] = f'awaiting_new_message_text:{channel_id}:{message_index}'
                await message.reply_text(
                    f"⏭️ Skipped media.\n\n"
                    f"🎯 Now send the text message for '{message_data.get('name', 'New Message')}'.\n"
                    f"🎯 AI Pattern Detection Active\n"
                    f"🎯 Bot will auto-convert emojis to premium!\n\n"
                    f"Or send /skip to skip text (media only message)."
                )
                return
            
            if message.photo:
                media_item = {
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id
                }
            elif message.video:
                media_item = {
                    'type': 'video',
                    'file_id': message.video.file_id
                }
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                
                if any(ext in file_name for ext in ['.apk', '.exe', '.zip', '.rar', '.pdf', '.html', '.htm', '.txt', '.doc', '.docx', '.xls', '.xlsx']):
                    media_item = {
                        'type': 'document',
                        'file_id': message.document.file_id,
                        'file_name': file_name
                    }
                elif mime_type.startswith('image/'):
                    media_item = {
                        'type': 'photo',
                        'file_id': message.document.file_id
                    }
                elif mime_type.startswith('video/'):
                    media_item = {
                        'type': 'video',
                        'file_id': message.document.file_id
                    }
                else:
                    media_item = {
                        'type': 'document',
                        'file_id': message.document.file_id,
                        'file_name': file_name
                    }
            elif message.animation:
                media_item = {
                    'type': 'animation', 
                    'file_id': message.animation.file_id
                }
            else:
                await message.reply_text("❌ Unsupported file type!")
                return
            
            if media_item:
                message_data['media_items'].append(media_item)
                self.update_custom_break_message(channel_id, message_index, message_data)
                
                media_count = len(message_data['media_items'])
                file_type = media_item.get('type', 'file')
                file_name = media_item.get('file_name', f"{file_type} {media_count}")
                
                await message.reply_text(
                    f"✅ {file_type.upper()} added: {file_name}\n"
                    f"Total files: {media_count}\n\n"
                    f"Send more files or type /done to finish adding media."
                )
            
        # Handle /done command for media
        elif state.startswith('awaiting_new_message_media:') and text == '/done':
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            media_count = len(message_data.get('media_items', []))
            
            self.user_state[chat_id] = f'awaiting_new_message_text:{channel_id}:{message_index}'
            
            await message.reply_text(
                f"✅ Added {media_count} media items.\n\n"
                f"🎯 Now send the text message for '{message_data.get('name', 'New Message')}'.\n"
                f"🎯 AI Pattern Detection Active\n"
                f"🎯 Bot will auto-convert emojis to premium!\n\n"
                f"Or send /skip to skip text (media only message)."
            )
            
        # Handle text for new message
        elif state.startswith('awaiting_new_message_text:') and (text or text == '/skip'):
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            
            if text == '/skip':
                message_data['text_content'] = ''
                await message.reply_text(
                    f"✅ Message '{message_data.get('name', 'New Message')}' created successfully!\n\n"
                    f"• Media: {len(message_data.get('media_items', []))} items\n"
                    f"• Text: None (media only)\n\n"
                    f"Message will be sent after break with a delay."
                )
            else:
                converted_text = self.auto_detect_and_convert_message(text)
                message_data['text_content'] = converted_text
                
                emojis_converted = []
                for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                    if placeholder in converted_text:
                        emojis_converted.append(f"{emoji} -> {placeholder}")
                
                media_count = len(message_data.get('media_items', []))
                text_len = len(converted_text)
                
                response_text = f"✅ Message '{message_data.get('name', 'New Message')}' created successfully!\n\n"
                response_text += f"• Media: {media_count} items\n"
                response_text += f"• Text: {text_len} characters\n"
                
                if emojis_converted:
                    response_text += f"• Emojis auto-converted: {', '.join(emojis_converted[:5])}"
                    if len(emojis_converted) > 5:
                        response_text += f" and {len(emojis_converted) - 5} more"
                
                response_text += f"\n\nMessage will be sent after break with a delay."
                
                await message.reply_text(response_text)
            
            self.update_custom_break_message(channel_id, message_index, message_data)
            del self.user_state[chat_id]
            
        # Handle edit message media
        elif state.startswith('awaiting_edit_message_media:') and (message.photo or message.video or message.document or message.animation):
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                await message.reply_text("❌ Message not found!")
                del self.user_state[chat_id]
                return
            
            message_data['media_items'] = []
            
            if message.photo:
                media_item = {
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id
                }
            elif message.video:
                media_item = {
                    'type': 'video',
                    'file_id': message.video.file_id
                }
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                
                if any(ext in file_name for ext in ['.apk', '.exe', '.zip', '.rar', '.pdf', '.html', '.htm', '.txt', '.doc', '.docx', '.xls', '.xlsx']):
                    media_item = {
                        'type': 'document',
                        'file_id': message.document.file_id,
                        'file_name': file_name
                    }
                elif mime_type.startswith('image/'):
                    media_item = {
                        'type': 'photo',
                        'file_id': message.document.file_id
                    }
                elif mime_type.startswith('video/'):
                    media_item = {
                        'type': 'video',
                        'file_id': message.document.file_id
                    }
                else:
                    media_item = {
                        'type': 'document',
                        'file_id': message.document.file_id,
                        'file_name': file_name
                    }
            elif message.animation:
                media_item = {
                    'type': 'animation', 
                    'file_id': message.animation.file_id
                }
            else:
                await message.reply_text("❌ Unsupported file type!")
                return
            
            if media_item:
                message_data['media_items'].append(media_item)
                self.update_custom_break_message(channel_id, message_index, message_data)
                
                media_count = len(message_data['media_items'])
                file_type = media_item.get('type', 'file')
                file_name = media_item.get('file_name', f"{file_type} {media_count}")
                
                await message.reply_text(
                    f"✅ {file_type.upper()} added: {file_name}\n"
                    f"Total files: {media_count}\n\n"
                    f"Send more files or type /done to finish."
                )
                
        # Handle /done for edit media
        elif state.startswith('awaiting_edit_message_media:') and text == '/done':
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            media_count = len(message_data.get('media_items', []))
            
            await message.reply_text(
                f"✅ Media updated for message {message_index+1}!\n"
                f"Total media items: {media_count}"
            )
            del self.user_state[chat_id]
            
        # Handle edit message text
        elif state.startswith('awaiting_edit_message_text:') and text:
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                await message.reply_text("❌ Message not found!")
                del self.user_state[chat_id]
                return
            
            converted_text = self.auto_detect_and_convert_message(text)
            message_data['text_content'] = converted_text
            self.update_custom_break_message(channel_id, message_index, message_data)
            
            emojis_converted = []
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if placeholder in converted_text:
                    emojis_converted.append(f"{emoji}")
            
            text_len = len(converted_text)
            response_text = f"✅ Text updated for message {message_index+1}!\n"
            response_text += f"Text length: {text_len} characters\n"
            
            if emojis_converted:
                response_text += f"Emojis auto-converted: {', '.join(emojis_converted[:5])}"
                if len(emojis_converted) > 5:
                    response_text += f" and {len(emojis_converted) - 5} more"
            
            await message.reply_text(response_text)
            del self.user_state[chat_id]
            
        # Break delay setup
        elif state.startswith('awaiting_break_delay:') and text:
            channel_id = state.split(':', 1)[1]
            
            try:
                delay = int(text)
                if 1 <= delay <= 60:
                    channel_config = self.get_channel_config(channel_id)
                    channel_config['custom_break_delay'] = delay
                    self.update_channel_config(channel_id, channel_config)
                    
                    await message.reply_text(f"✅ Custom break message delay set to {delay} minutes for {channel_id}!")
                else:
                    await message.reply_text("❌ Delay must be between 1 and 60 minutes!")
            except ValueError:
                await message.reply_text("❌ Please enter a valid number!")
                
            del self.user_state[chat_id]
            
        # Channel-specific configurations
        elif state.startswith('awaiting_register_link:') and text:
            channel_id = state.split(':', 1)[1]
            self.update_channel_config(channel_id, {'register_link': text})
            await message.reply_text(f"✅ Register link updated for {channel_id}!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_promo_text:') and text:
            channel_id = data.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {'promotional_text': converted_text})
            await message.reply_text(f"✅ Promotional text updated for {channel_id}!\n🎯 Emojis were auto-converted.")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_prediction_template:') and text:
            channel_id = data.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {
                'templates': {'prediction_header': converted_text}
            })
            await message.reply_text(f"✅ Prediction template updated for {channel_id}!\n🎯 Emojis were auto-converted.")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_morning_template:') and text:
            channel_id = data.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {
                'templates': {'good_morning': converted_text}
            })
            await message.reply_text(f"✅ Morning template updated for {channel_id}!\n🎯 Emojis were auto-converted.")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_night_template:') and text:
            channel_id = data.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {
                'templates': {'good_night': converted_text}
            })
            await message.reply_text(f"✅ Night template updated for {channel_id}!\n🎯 Emojis were auto-converted.")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_break_template:') and text:
            channel_id = data.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {
                'templates': {'break_message': converted_text}
            })
            await message.reply_text(f"✅ Break template updated for {channel_id}!\n🎯 Emojis were auto-converted.")
            del self.user_state[chat_id]

    async def main_loop(self, context: ContextTypes.DEFAULT_TYPE):
        """Main loop with AI Pattern Recognition"""
        logging.info("🚀 Bot started - REAL AI PATTERN RECOGNITION")
        logging.info("🎯 FEATURE: GPT-4/Claude like pattern learning")
        logging.info("🎯 TARGET: Win Rate 80-85%+")
        logging.info("🎨 FEATURE: Multiple Custom Break Messages")
        logging.info("⏯️ FEATURE: Individual Channel Prediction Control")
        logging.info("🤖 AI: Learns from every result")
        
        if self.use_user_account:
            success = await self.initialize_user_client()
            if success:
                logging.info("✅ User account ready for premium emojis")
            else:
                logging.warning("⚠️ Using regular emojis")
        
        while True:
            try:
                if not self.active_channels:
                    await asyncio.sleep(60)
                    continue
                
                current_session, is_active_period, current_hour, current_minute, next_session = self.get_current_session()
                is_operational = self.is_operational_time(current_hour, current_minute)
                
                logging.info(f"🕒 Time: {current_hour:02d}:{current_minute:02d}, Active: {is_active_period}, Session: {current_session}")
                
                # Morning message
                if current_hour == 6 and current_minute == 0 and not self.morning_message_sent:
                    await self.send_good_morning_message(context)
                    self.morning_message_sent = True
                    self.night_message_sent = False
                    self.session_ended = False
                    self.in_break_period = False
                    self.break_message_sent = False
                    self.waiting_for_result = False
                    self.last_result_was_win = False
                    self.waiting_for_win = False
                    self.session_predictions = []
                    self.session_wins = 0
                    self.session_losses = 0
                    self.consecutive_losses = 0
                    self.consecutive_wins = 0
                    self.big_small_history.clear()
                    logging.info("🔄 Morning reset complete")
                
                # Night message
                if current_hour == 23 and current_minute >= 45 and not self.night_message_sent:
                    await self.send_good_night_message(context)
                    self.night_message_sent = True
                    self.morning_message_sent = False
                    self.session_ended = True
                    self.in_break_period = True
                
                if not is_operational:
                    if not self.night_mode:
                        self.night_mode = True
                        logging.info("🌙 Night mode activated")
                    await asyncio.sleep(60)
                    continue
                else:
                    if self.night_mode:
                        self.night_mode = False
                        logging.info("☀️ Day mode activated")
                
                # Session change detection
                if current_session != self.current_session:
                    logging.info(f"🔄 Session changed: {self.current_session} -> {current_session}")
                    
                    if is_active_period:
                        if self.in_break_period or self.session_ended:
                            logging.info("🎯 Starting new active session")
                            self.in_break_period = False
                            self.break_message_sent = False
                            self.session_ended = False
                            self.waiting_for_result = False
                            self.last_result_was_win = False
                            self.waiting_for_win = False
                            self.session_predictions = []
                            self.current_prediction_period = None
                            self.current_prediction_choice = None
                            
                            self.current_session = current_session
                            await self.send_new_session_message(context)
                    else:
                        if not self.in_break_period and not self.break_message_sent:
                            logging.info("⏰ Session ended, checking for break...")
                            
                            if len(self.session_predictions) > 0:
                                if self.last_result_was_win:
                                    logging.info("🎯 Last was WIN - Sending break message")
                                    await self.send_break_message(context, next_session)
                                    self.in_break_period = True
                                    self.break_message_sent = True
                                    self.session_ended = True
                                    self.waiting_for_win = False
                                    self.last_result_was_win = False
                                    
                                    self.session_predictions = []
                                    self.current_prediction_period = None
                                    self.current_prediction_choice = None
                                    self.waiting_for_result = False
                                else:
                                    logging.info("🔄 Last was LOSS - Continuing until WIN")
                                    self.waiting_for_win = True
                                    self.in_break_period = False
                                    self.session_ended = False
                            else:
                                logging.info("📝 No predictions - Normal break")
                                await self.send_break_message(context, next_session)
                                self.in_break_period = True
                                self.break_message_sent = True
                                self.session_ended = True
                                self.waiting_for_win = False
                    
                    self.current_session = current_session
                
                # Fetch data and process predictions - ONLY FOR ACTIVE CHANNELS
                if is_operational and self.active_channels:
                    data = await self.fetch_live_data()
                    
                    if not data:
                        await asyncio.sleep(10)
                        continue
                    
                    # Check if ANY channel has active predictions
                    active_channel_count = len([c for c in self.active_channels if self.is_channel_prediction_active(c)])
                    
                    if active_channel_count == 0:
                        logging.info("⏸️ All channel predictions paused, skipping predictions")
                        await asyncio.sleep(30)
                        continue
                    
                    # NORMAL ACTIVE PERIOD
                    if is_active_period and not self.session_ended and not self.in_break_period:
                        if self.waiting_for_result:
                            await self.check_result_and_send_next(context, data)
                        else:
                            await self.send_first_prediction(context, data)
                    
                    # BREAK PERIOD BUT WAITING FOR WIN
                    elif not is_active_period and self.waiting_for_win and not self.in_break_period:
                        logging.info("🎯 Break period - Continuing for WIN")
                        if self.waiting_for_result:
                            result_sent = await self.check_result_and_send_next(context, data)
                            if result_sent:
                                if self.last_result_was_win:
                                    logging.info("🎯 Got WIN - Now breaking")
                                    await self.send_break_message(context, next_session)
                                    self.in_break_period = True
                                    self.break_message_sent = True
                                    self.session_ended = True
                                    self.waiting_for_win = False
                                    self.last_result_was_win = False
                                    
                                    self.session_predictions = []
                                    self.current_prediction_period = None
                                    self.current_prediction_choice = None
                                    self.waiting_for_result = False
                                else:
                                    await self.send_first_prediction(context, data)
                        else:
                            await self.send_first_prediction(context, data)
                    
                    # NORMAL BREAK PERIOD
                    elif not is_active_period and self.in_break_period:
                        logging.info("⏸️ In break period - Waiting")
                        await asyncio.sleep(30)
                
                # Periodically save AI model
                if self.ai_total_predictions % 25 == 0 and self.ai_total_predictions > 0:
                    self.save_ai_model()
                
                await asyncio.sleep(10)
                
            except Exception as e:
                logging.error(f"❌ Loop error: {e}")
                import traceback
                logging.error(traceback.format_exc())
                await asyncio.sleep(30)

    def run(self):
        application = Application.builder().token(self.bot_token).build()
        
        application.add_handler(CommandHandler(["start", "admin"], self.start))
        application.add_handler(CallbackQueryHandler(self.handle_callback))
        application.add_handler(MessageHandler(filters.ALL, self.handle_message))
        
        job_queue = application.job_queue
        job_queue.run_once(lambda context: asyncio.create_task(self.main_loop(context)), 5)
        
        logging.info("🚀 WinGo Bot Starting...")
        logging.info("🎯 REAL AI PATTERN RECOGNITION SYSTEM")
        logging.info("• GPT-4/Claude like pattern learning")
        logging.info("• Target Win Rate: 80-85%+")
        logging.info("• Learns from every result")
        logging.info("⏯️ FEATURE: PER-CHANNEL PREDICTION CONTROL")
        logging.info("🎨 FEATURE: MULTIPLE CUSTOM BREAK MESSAGES")
        logging.info("🤖 AI: Random Forest Classifier with 100 estimators")
        logging.info("📎 SUPPORT: ANY File Type (APK, PDF, HTML, EXE, ZIP, etc.)")
        logging.info("🎯 CONTROL: Start/Pause predictions for each channel individually")
        logging.info("⚡ AI: Auto-saves and retrains periodically")
        
        application.run_polling()

if __name__ == "__main__":
    BOT_TOKEN = "8030162642:AAG4Gbe2pyQv8ZreGyw8vTEhKvVKY2Eiugw"
    
    API_ID = 21538384
    API_HASH = "9b8e9b10a5c34b67054aceca02bf423e"
    PHONE = "+919341451832"
    
    bot = WinGoBotEnhanced(BOT_TOKEN, api_id=API_ID, api_hash=API_HASH, phone=PHONE)
    bot.run()