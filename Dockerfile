# Playwright-এর অফিসিয়াল ইমেজ ব্যবহার করা হচ্ছে (এতে ক্রোমিয়াম ও সিস্টেম ডিপেন্ডেন্সি আগে থেকেই আছে)
FROM mcr.microsoft.com/playwright/python:v1.42.0-jammy

# ওয়ার্কিং ডিরেক্টরি সেট করা
WORKDIR /app

# requirements.txt কপি করে পাইথন প্যাকেজ ইনস্টল করা
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# পুরো প্রজেক্ট কপি করা
COPY . .

# Render ডিফল্টভাবে 8080 পোর্ট ব্যবহার করে
EXPOSE 8080

# বট রান করার কমান্ড
CMD ["python", "bot.py"]
