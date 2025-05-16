package com.example.projectsenseapp

import android.Manifest
import android.annotation.SuppressLint
import android.content.pm.PackageManager
import android.graphics.ImageFormat
import android.hardware.Camera
import android.os.Build
import android.os.Bundle
import android.os.Environment
import android.os.Handler
import android.os.Looper
import android.media.MediaScannerConnection
import android.util.Log
import android.view.SurfaceHolder
import android.view.SurfaceView
import android.widget.Button
import android.widget.TextView
import android.widget.Toast
import androidx.appcompat.app.AppCompatActivity
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import com.example.projectsenseapp.databinding.ActivityMainBinding
import java.io.File
import java.io.FileWriter
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.pow
import kotlin.math.sin
import kotlin.math.sqrt
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.widget.ImageView
import android.view.LayoutInflater
import android.widget.EditText
import java.io.ObjectOutputStream
import java.io.ObjectInputStream

import java.io.FileOutputStream
import java.io.FileInputStream

@SuppressLint("ClickableViewAccessibility", "Deprecated")
class MainActivity : AppCompatActivity(), SurfaceHolder.Callback {
    private val USER_DATA_FILE = "user_heart_data.dat"
    private var userName = "Гость"
    private var userHeartData = mutableListOf<HeartRateMeasurement>()

    // Класс для хранения данных измерения
    data class HeartRateMeasurement(
        val timestamp: Long = System.currentTimeMillis(),
        val heartRate: Int,
        val confidence: Double,
        val signalQuality: Double,
        val redValues: List<Double> = emptyList()
    )

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        binding = ActivityMainBinding.inflate(layoutInflater)
        setContentView(binding.root)

        // Загружаем сохраненные данные
        loadUserData()

        // Если имя не сохранено, запрашиваем
        if (userName == "Гость") {
            askForUserName()
        } else {
            binding.userNameText.text = "Пользователь: $userName"
        }
    private val TAG = "HeartRateMonitor"
    private val REQUEST_CAMERA_PERMISSION = 100
    private val REQUEST_STORAGE_PERMISSION = 101

    private var camera: Camera? = null
    private var surfaceHolder: SurfaceHolder? = null
    private var processing = AtomicBoolean(false)
    private var flashEnabled = false

    // Добавляем переменную для хранения последнего валидного пульса
    private var lastValidHeartRate = 70 // Стандартный пульс 70 уд/мин по умолчанию
    private var heartRateConfidence = 0.0 // Достоверность измерения от 0 до 1

    private lateinit var binding: ActivityMainBinding

    // Данные для обработки
    private val redChannelValues = mutableListOf<Double>()
    private val greenChannelValues = mutableListOf<Double>()
    private val blueChannelValues = mutableListOf<Double>()
    private val timeValues = mutableListOf<Long>()
    private var startTime: Long = 0

    // Улучшенные параметры обработки
    private val FRAMES_TO_PROCESS = 350
    private val MOVING_WINDOW_SIZE = 20
    private val REALTIME_UPDATE_WINDOW = 120
    private val REALTIME_UPDATE_INTERVAL = 100L
    private val MIN_VALID_HEART_RATE = 40
    private val MAX_VALID_HEART_RATE = 200

    // Новые параметры для фильтрации
    private val LOW_CUTOFF_FREQ = 0.5
    private val HIGH_CUTOFF_FREQ = 3.3
    private val QUALITY_THRESHOLD = 0.25

    // Скользящие средние для быстрой оценки качества сигнала
    private val signalQualityWindow = 20
    private val recentVariances = mutableListOf<Double>()
    private var signalQuality = 0.0 // От 0 до 1

    // Для ручного измерения пульса
    private val manualPulseTimestamps = mutableListOf<Long>()
    private var manualHeartRate = 0
    private var manualHeartRateConfidence = 0.0
    private val manualHeartRateHandler = Handler(Looper.getMainLooper())
    private val manualHeartRateRunnable = object : Runnable {
        override fun run() {
            // Удаляем старые метки (старше 15 секунд)
            val currentTime = System.currentTimeMillis()
            while (manualPulseTimestamps.isNotEmpty() && currentTime - manualPulseTimestamps[0] > 15000) {
                manualPulseTimestamps.removeAt(0)
            }

            // Обновляем отображение пульса, если есть достаточно данных
            if (manualPulseTimestamps.size >= 2) {
                updateManualHeartRate()
            }

            // Сравниваем результаты
            compareHeartRateMeasurements()

            // Продолжаем обновление каждую секунду
            manualHeartRateHandler.postDelayed(this, 1000)
        }
    }

    private val updateHandler = Handler(Looper.getMainLooper())
    private val updateRunnable = object : Runnable {
        override fun run() {
            if (processing.get()) {
                updateRealtimeHeartRate()
                updateHandler.postDelayed(this, REALTIME_UPDATE_INTERVAL)
            }
        }
    }

    // Режим непрерывного измерения
    private var continuousMode = true

    // Добавляем переменную для управления записью данных
    private var isRecordingData = false
    private var recordedData = StringBuilder()

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        binding = ActivityMainBinding.inflate(layoutInflater)
        setContentView(binding.root)

        // Добавляем обработчик долгого нажатия на кнопку измерения
        binding.startButton.setOnLongClickListener {
            toggleDataRecording()
            true
        }

        // Настройка SurfaceView
        surfaceHolder = binding.previewSurface.holder
        surfaceHolder?.addCallback(this)

        binding.startButton.setOnClickListener {
            if (processing.get()) {
                stopHeartRateReading()
            } else {
                checkCameraPermissionAndStart()
            }
        }

        // Добавляем кнопку для включения/выключения вспышки
        binding.flashButton.setOnClickListener {
            toggleFlash()
        }

        // Кнопка для ручного измерения пульса
        binding.manualPulseButton.setOnClickListener {
            recordManualPulse()
        }

        // Добавляем TextView для отображения сравнения результатов
        binding.comparisonText = TextView(this).apply {
            text = "Сравнение: --"
        }

        // Запускаем обработчик для ручного измерения пульса
        manualHeartRateHandler.post(manualHeartRateRunnable)
    }

    private fun compareHeartRateMeasurements() {
        if (manualHeartRate == 0 || lastValidHeartRate == 0) return

        val difference = abs(manualHeartRate - lastValidHeartRate)
        val avgHeartRate = (manualHeartRate + lastValidHeartRate) / 2
        val percentageDifference = (difference.toDouble() / avgHeartRate) * 100

        val comparisonText = when {
            difference <= 5 -> "Отличное совпадение (разница: $difference уд/мин)"
            difference <= 10 -> "Хорошее совпадение (разница: $difference уд/мин)"
            difference <= 15 -> "Умеренное совпадение (разница: $difference уд/мин)"
            else -> "Большая разница (разница: $difference уд/мин)"
        }

        runOnUiThread {
            binding.comparisonText.text = "Сравнение: $comparisonText\n" +
                    "Камера: $lastValidHeartRate уд/мин\n" +
                    "Ручной: $manualHeartRate уд/мин"
        }

        Log.d(TAG, "Сравнение измерений: $comparisonText (${"%.1f".format(percentageDifference)}%)")
    }

    private fun toggleFlash() {
        if (camera != null) {
            try {
                val parameters = camera?.parameters
                if (flashEnabled) {
                    parameters?.flashMode = Camera.Parameters.FLASH_MODE_OFF
                    binding.flashButton.text = "Включить подсветку"
                } else {
                    parameters?.flashMode = Camera.Parameters.FLASH_MODE_TORCH
                    binding.flashButton.text = "Выключить подсветку"
                }
                camera?.parameters = parameters
                flashEnabled = !flashEnabled
            } catch (e: Exception) {
                Log.e(TAG, "Ошибка при управлении вспышкой: ${e.message}")
                Toast.makeText(this, "Ошибка при управлении вспышкой", Toast.LENGTH_SHORT).show()
            }
        }
    }

    private fun checkCameraPermissionAndStart() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA)
            != PackageManager.PERMISSION_GRANTED) {
            ActivityCompat.requestPermissions(
                this,
                arrayOf(Manifest.permission.CAMERA),
                REQUEST_CAMERA_PERMISSION
            )
        } else {
            startHeartRateReading()
        }
    }

    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<out String>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQUEST_CAMERA_PERMISSION) {
            if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
                startHeartRateReading()
            } else {
                Toast.makeText(
                    this,
                    "Разрешение на использование камеры необходимо для работы приложения",
                    Toast.LENGTH_LONG
                ).show()
            }
        } else if (requestCode == REQUEST_STORAGE_PERMISSION) {
            if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
                toggleDataRecording()
            } else {
                Toast.makeText(
                    this,
                    "Разрешение на хранение данных необходимо для записи отладочной информации",
                    Toast.LENGTH_LONG
                ).show()
            }
        }
    }

    private fun startHeartRateReading() {
        if (processing.compareAndSet(false, true)) {
            // Очищаем данные от предыдущего измерения
            redChannelValues.clear()
            greenChannelValues.clear()
            blueChannelValues.clear()
            timeValues.clear()
            startTime = System.currentTimeMillis()

            binding.startButton.text = "Остановить"
            binding.pulseRateText.text = "-- уд/мин"

            try {
                camera = Camera.open()
                val parameters = camera?.parameters

                // Устанавливаем минимальное разрешение для ускорения обработки
                val smallestSize = parameters?.supportedPreviewSizes?.minByOrNull {
                    it.width * it.height
                }
                smallestSize?.let {
                    parameters?.setPreviewSize(it.width, it.height)
                }

                // Устанавливаем формат изображения и частоту кадров
                parameters?.previewFormat = ImageFormat.NV21

                // Максимальная частота кадров для лучшей точности
                val fpsRanges = parameters?.supportedPreviewFpsRange
                fpsRanges?.maxByOrNull { it[Camera.Parameters.PREVIEW_FPS_MAX_INDEX] }?.let {
                    parameters?.setPreviewFpsRange(it[Camera.Parameters.PREVIEW_FPS_MIN_INDEX],
                        it[Camera.Parameters.PREVIEW_FPS_MAX_INDEX])
                }

                // Автоматически включаем вспышку при начале измерения
                if (hasFlash()) {
                    parameters?.flashMode = Camera.Parameters.FLASH_MODE_TORCH
                    flashEnabled = true
                    binding.flashButton.text = "Выключить подсветку"
                }

                camera?.parameters = parameters

                // Настраиваем обратный вызов для обработки кадров
                camera?.setPreviewCallback { data, _ ->
                    processImageData(data)
                }

                // Запускаем предварительный просмотр
                camera?.setPreviewDisplay(surfaceHolder)
                camera?.startPreview()

                // Запускаем обновление пульса в реальном времени
                updateHandler.postDelayed(updateRunnable, REALTIME_UPDATE_INTERVAL)

            } catch (e: Exception) {
                Log.e(TAG, "Ошибка запуска камеры: ${e.message}")
                stopHeartRateReading()
                Toast.makeText(this, "Ошибка запуска камеры", Toast.LENGTH_SHORT).show()
            }
        }
    }

    private fun hasFlash(): Boolean {
        return packageManager.hasSystemFeature(PackageManager.FEATURE_CAMERA_FLASH)
    }

    private fun stopHeartRateReading() {
        if (processing.compareAndSet(true, false)) {
            // Останавливаем обновление пульса в реальном времени
            updateHandler.removeCallbacks(updateRunnable)

            binding.startButton.text = "Начать измерение"

            // Выключаем светодиод при остановке измерения
            if (flashEnabled) {
                try {
                    val parameters = camera?.parameters
                    parameters?.flashMode = Camera.Parameters.FLASH_MODE_OFF
                    camera?.parameters = parameters
                    flashEnabled = false
                    binding.flashButton.text = "Включить подсветку"
                } catch (e: Exception) {
                    Log.e(TAG, "Ошибка при выключении вспышки: ${e.message}")
                }
            }

            camera?.setPreviewCallback(null)
            camera?.stopPreview()
            camera?.release()
            camera = null

            // Если достаточно данных, вычисляем пульс
            if (timeValues.size > MOVING_WINDOW_SIZE) {
                calculateHeartRate()
            }
        }
    }

    private fun processImageData(data: ByteArray) {
        if (!processing.get()) return

        val width = camera?.parameters?.previewSize?.width ?: return
        val height = camera?.parameters?.previewSize?.height ?: return

        // Анализируем центральную область изображения
        val centerX = width / 2
        val centerY = height / 2
        val windowSize = minOf(width, height) / 4

        var redSum = 0.0
        var greenSum = 0.0
        var blueSum = 0.0
        var sampleCount = 0

        // Добавляем оценку стандартного отклонения для определения текстуры
        var redSquareSum = 0.0

        // Извлекаем U и V значения (цветовые компоненты)
        val uvOffset = width * height

        for (y in centerY - windowSize until centerY + windowSize) {
            for (x in centerX - windowSize until centerX + windowSize) {
                if (y >= 0 && y < height && x >= 0 && x < width) {
                    val yIndex = y * width + x

                    if (yIndex < data.size) {
                        val yValue = data[yIndex].toInt() and 0xFF

                        val uvIndex = uvOffset + (y / 2) * width + (x and 1.inv())

                        if (uvIndex + 1 < data.size) {
                            val uValue = (data[uvIndex].toInt() and 0xFF) - 128
                            val vValue = (data[uvIndex + 1].toInt() and 0xFF) - 128

                            val r = yValue + 1.370705 * vValue
                            val g = yValue - 0.337633 * uValue - 0.698001 * vValue
                            val b = yValue + 1.732446 * uValue

                            val rClamped = maxOf(0.0, minOf(255.0, r))

                            redSum += rClamped
                            greenSum += maxOf(0.0, minOf(255.0, g))
                            blueSum += maxOf(0.0, minOf(255.0, b))
                            redSquareSum += rClamped * rClamped

                            sampleCount++
                        } else {
                            redSum += yValue.toDouble()
                            greenSum += yValue.toDouble() * 0.7
                            blueSum += yValue.toDouble() * 0.5
                            redSquareSum += yValue.toDouble() * yValue.toDouble()
                            sampleCount++
                        }
                    }
                }
            }
        }

        if (sampleCount > 0) {
            val avgRed = redSum / sampleCount
            val avgGreen = greenSum / sampleCount
            val avgBlue = blueSum / sampleCount

            // Вычисляем стандартное отклонение для красного канала (показатель текстуры)
            val redVariance = (redSquareSum / sampleCount) - (avgRed * avgRed)
            val redStdDev = sqrt(maxOf(0.0, redVariance))

            val currentTime = System.currentTimeMillis() - startTime

            // Логирование значений RGB каждые 50 кадров
            if (redChannelValues.size % 50 == 0) {
                Log.d(TAG, "RGB значения: R=${avgRed.toInt()}, G=${avgGreen.toInt()}, B=${avgBlue.toInt()}, StdDev=${redStdDev.toInt()}")
            }

            // Записываем данные, если включена запись
            if (isRecordingData) {
                recordedData.append("$currentTime,${avgRed.toInt()},${avgGreen.toInt()},${avgBlue.toInt()},${(signalQuality * 100).toInt()}\n")
            }

            redChannelValues.add(avgRed)
            greenChannelValues.add(avgGreen)
            blueChannelValues.add(avgBlue)
            timeValues.add(currentTime)

            updateSignalQuality()

            // В непрерывном режиме не останавливаем сбор данных автоматически
            if (redChannelValues.size >= FRAMES_TO_PROCESS && !continuousMode) {
                runOnUiThread { stopHeartRateReading() }
            } else {
                // Если собрали достаточно данных для анализа, начинаем удалять старые данные
                if (redChannelValues.size > FRAMES_TO_PROCESS) {
                    redChannelValues.removeAt(0)
                    greenChannelValues.removeAt(0)
                    blueChannelValues.removeAt(0)
                    timeValues.removeAt(0)
                }
            }
        }
    }


    /**
     * Оценка качества сигнала на основе вариации последних значений
     */
    private fun updateSignalQuality() {
        if (redChannelValues.size < signalQualityWindow + 1) return

        val recentRed = redChannelValues.takeLast(signalQualityWindow)
        val mean = recentRed.average()

        // Вычисляем дисперсию
        val variance = recentRed.map { (it - mean).pow(2) }.average()

        // Нормализованная дисперсия как показатель качества
        val normalizedVariance = minOf(1.0, variance / 100.0)

        recentVariances.add(normalizedVariance)
        if (recentVariances.size > 5) recentVariances.removeAt(0)

        // Улучшенная оценка качества сигнала с более низкими требованиями
        signalQuality = when {
            normalizedVariance < 0.03 -> 0.1 // Слишком стабильный сигнал - нет пульса
            normalizedVariance < 0.7 -> 0.9 // Хороший диапазон - увеличен верхний порог
            else -> 0.3 // Сильные помехи, но все равно пробуем использовать
        }

        // Логируем качество сигнала
        if (redChannelValues.size % 50 == 0) {
            Log.d(TAG, "Качество сигнала: ${(signalQuality * 100).toInt()}%, вариация: ${(normalizedVariance * 100).toInt()}%")
        }
    }

        // Функция для запроса имени пользователя
        private fun askForUserName() {
            val dialogView = LayoutInflater.from(this).inflate(R.layout.dialog_user_name, null)
            val editText = dialogView.findViewById<EditText>(R.id.userNameEditText)

            AlertDialog.Builder(this)
                .setTitle("Введите ваше имя")
                .setView(dialogView)
                .setPositiveButton("Сохранить") { _, _ ->
                    userName = editText.text.toString().takeIf { it.isNotBlank() } ?: "Гость"
                    binding.userNameText.text = "Пользователь: $userName"
                    saveUserData()
                }
                .setCancelable(false)
                .show()
        }

        // Функция для отрисовки графика пульса
        private fun drawHeartRateGraph(values: List<Double>, imageView: ImageView) {
            if (values.size < 2) return

            val width = imageView.width
            val height = imageView.height
            if (width <= 0 || height <= 0) return

            val bitmap = Bitmap.createBitmap(width, height, Bitmap.Config.ARGB_8888)
            val canvas = Canvas(bitmap)

            // Рисуем фон
            val backgroundPaint = Paint().apply {
                color = Color.WHITE
                style = Paint.Style.FILL
            }
            canvas.drawRect(0f, 0f, width.toFloat(), height.toFloat(), backgroundPaint)

            // Настраиваем кисть для графика
            val graphPaint = Paint().apply {
                color = Color.RED
                strokeWidth = 3f
                style = Paint.Style.STROKE
                isAntiAlias = true
            }

            // Нормализуем данные
            val maxValue = values.maxOrNull() ?: 1.0
            val minValue = values.minOrNull() ?: 0.0
            val range = maxValue - minValue
            if (range <= 0) return

            // Рисуем график
            val path = Path()
            val stepX = width.toFloat() / (values.size - 1)

            values.forEachIndexed { index, value ->
                val x = index * stepX
                val y = height - ((value - minValue) / range * height * 0.8f).toFloat() - height * 0.1f

                if (index == 0) {
                    path.moveTo(x, y)
                } else {
                    path.lineTo(x, y)
                }
            }

            canvas.drawPath(path, graphPaint)
            imageView.setImageBitmap(bitmap)
        }

        // Сохраняем измерение
        private fun saveMeasurement(heartRate: Int) {
            val measurement = HeartRateMeasurement(
                heartRate = heartRate,
                confidence = heartRateConfidence,
                signalQuality = signalQuality,
                redValues = redChannelValues.takeLast(100) // Сохраняем последние 100 значений
            )

            userHeartData.add(measurement)
            saveUserData()

            // Обновляем график
            drawHeartRateGraph(measurement.redValues, binding.heartRateGraph)

            // Добавляем запись в историю
            val timeString = SimpleDateFormat("HH:mm:ss", Locale.getDefault()).format(Date(measurement.timestamp))
            binding.measurementHistory.append("$timeString - ${measurement.heartRate} уд/мин\n")
        }

        // Сохраняем данные пользователя
        private fun saveUserData() {
            try {
                val file = File(filesDir, USER_DATA_FILE)
                ObjectOutputStream(FileOutputStream(file)).use { oos ->
                    oos.writeObject(userName)
                    oos.writeObject(userHeartData)
                }
            } catch (e: Exception) {
                Log.e(TAG, "Ошибка сохранения данных: ${e.message}")
            }
        }

        // Загружаем данные пользователя
        private fun loadUserData() {
            try {
                val file = File(filesDir, USER_DATA_FILE)
                if (file.exists()) {
                    ObjectInputStream(FileInputStream(file)).use { ois ->
                        userName = ois.readObject() as? String ?: "Гость"
                        @Suppress("UNCHECKED_CAST")
                        userHeartData = (ois.readObject() as? MutableList<HeartRateMeasurement>) ?: mutableListOf()
                    }

                    // Восстанавливаем последнее измерение
                    userHeartData.lastOrNull()?.let { lastMeasurement ->
                        lastValidHeartRate = lastMeasurement.heartRate
                        heartRateConfidence = lastMeasurement.confidence
                        drawHeartRateGraph(lastMeasurement.redValues, binding.heartRateGraph)
                    }
                }
            } catch (e: Exception) {
                Log.e(TAG, "Ошибка загрузки данных: ${e.message}")
            }
        }

        // В методе calculateHeartRate() заменяем вывод на:
        private fun calculateHeartRate() {
            if (redChannelValues.size < MOVING_WINDOW_SIZE * 2) {
                runOnUiThread {
                    binding.pulseRateText.text = "Недостаточно данных"
                    Toast.makeText(this, "Недостаточно данных для определения пульса", Toast.LENGTH_LONG).show()
                }
                return
            }

            val heartRate = getHeartRateFromPeaks(redChannelValues, timeValues)

            runOnUiThread {
                if (heartRate > 0) {
                    lastValidHeartRate = heartRate
                    heartRateConfidence = minOf(1.0, signalQuality * 1.5)
                    binding.pulseRateText.text = "$heartRate уд/мин"
                    saveMeasurement(heartRate) // Сохраняем измерение
                } else {
                    binding.pulseRateText.text = "$lastValidHeartRate уд/мин (примерно)"
                    Toast.makeText(this, "Точное определение пульса не удалось", Toast.LENGTH_LONG).show()
                }
            }
        }

    /**
     * Функция для обновления значения пульса в реальном времени с упрощенным алгоритмом
     */




    private fun updateRealtimeHeartRate() {
        // Берем только последние данные для анализа в реальном времени
        val dataSize = redChannelValues.size
        if (dataSize < 10) {
            // Если данных мало, просто выходим из функции
            return
        }

        val startIndex = maxOf(0, dataSize - REALTIME_UPDATE_WINDOW)

        // Используем только красный канал для простоты
        val valuesForAnalysis = redChannelValues.subList(startIndex, dataSize)
        val timeValuesForAnalysis = timeValues.subList(startIndex, dataSize)

        // Логируем размер данных для анализа
        Log.d(TAG, "Анализ пульса в реальном времени: ${valuesForAnalysis.size} значений")

        // Получаем пульс методом спектрального анализа
        val heartRate = getHeartRateFromPeaks(valuesForAnalysis, timeValuesForAnalysis)

        // Если получили валидное значение пульса, сохраняем его
        if (heartRate > 0) {
            lastValidHeartRate = heartRate
            heartRateConfidence = minOf(1.0, signalQuality * 1.5) // Корректируем доверие к измерению
        } else {
            // Понижаем доверие к последнему измерению, если не получаем новых валидных данных
            heartRateConfidence = maxOf(0.1, heartRateConfidence * 0.9)
        }

        runOnUiThread {
            // Всегда показываем значение - либо новое, либо предыдущее валидное
            val displayHeartRate = if (heartRate > 0) heartRate else lastValidHeartRate
            binding.pulseRateText.text = "$displayHeartRate уд/мин"
        }
    }

    /**
     * Метод получения частоты пульса через спектральный анализ
     */
    private fun getHeartRateFromPeaks(values: List<Double>, timeValues: List<Long>): Int {
        if (values.size < 10) return 0 // Слишком мало данных

        // 1. Среднее значение красного канала - уже есть в values

        // 2. Интерполяция сигнала
        // Вычисляем интервал дискретизации
        val avgSamplingInterval = if (timeValues.size >= 2) {
            (timeValues.last() - timeValues.first()) / (timeValues.size - 1).toDouble()
        } else {
            33.0 // Примерно 30 кадров в секунду
        }

        Log.d(TAG, "Средний интервал дискретизации: $avgSamplingInterval мс")

        // 3. Разбиение на пересекающиеся отрезки
        // Используем все данные, но если их много, берем только последние 5 секунд
        val samplesInFiveSeconds = (5000 / avgSamplingInterval).toInt()
        val analysisValues = if (values.size > samplesInFiveSeconds) {
            values.takeLast(samplesInFiveSeconds)
        } else {
            values
        }

        Log.d(TAG, "Количество значений для анализа: ${analysisValues.size}")

        // Удаляем тренд (DC компонент) для лучшего спектрального анализа
        val mean = analysisValues.average()
        val detrended = analysisValues.map { it - mean }

        // 4. Вычисление спектра сигнала через БПФ
        // Простой способ получить доминирующую частоту - через автокорреляцию
        val autocorrelation = computeAutocorrelation(detrended)

        // Находим пики в автокорреляции, пропуская первый (он всегда на нуле)
        val acPeaks = findPeaksInAutocorrelation(autocorrelation)

        if (acPeaks.isEmpty()) {
            Log.d(TAG, "Не найдены пики в автокорреляции")
            return 0
        }

        // Берем первый пик как период сигнала
        val periodInSamples = acPeaks.first()

        // Переводим в частоту
        val frequencyInHz = 1000.0 / (periodInSamples * avgSamplingInterval)

        // Переводим в удары в минуту
        val bpm = (frequencyInHz * 60.0).toInt()

        Log.d(TAG, "Период в отсчетах: $periodInSamples, частота: ${"%.2f".format(frequencyInHz)} Гц, пульс: $bpm уд/мин")

        // 5. Валидация результата
        return if (bpm in 30..220) {
            bpm
        } else {
            Log.d(TAG, "Пульс $bpm вне допустимого диапазона")
            0
        }
    }

    /**
     * Вычисляет автокорреляцию сигнала
     */
    private fun computeAutocorrelation(signal: List<Double>): List<Double> {
        val n = signal.size
        val result = mutableListOf<Double>()

        // Вычисляем автокорреляцию только до половины длины сигнала
        val maxLag = n / 2

        for (lag in 0 until maxLag) {
            var sum = 0.0
            var count = 0

            for (i in 0 until n - lag) {
                sum += signal[i] * signal[i + lag]
                count++
            }

            // Нормализация
            if (count > 0) {
                result.add(sum / count)
            } else {
                result.add(0.0)
            }
        }

        return result
    }

    /**
     * Находит пики в автокорреляции (пропуская первый, который всегда на нуле)
     */
    private fun findPeaksInAutocorrelation(autocorrelation: List<Double>): List<Int> {
        if (autocorrelation.size < 5) return emptyList()

        val peaks = mutableListOf<Int>()

        // Игнорируем первые несколько лагов (из-за высокой автокорреляции на малых лагах)
        val minLag = 5
        // Берем только первые 3 секунды для поиска пиков (соответствует пульсу до 40 уд/мин)
        val maxLag = minOf(autocorrelation.size - 2, 90) // 90 лагов ≈ 3 секунды при 30 кадрах/с

        // Порог в процентах от максимального значения автокорреляции
        val maxValue = autocorrelation.take(maxLag).maxOrNull() ?: 0.0
        val threshold = maxValue * 0.5

        Log.d(TAG, "Поиск пиков в автокорреляции: порог=${"%.2f".format(threshold)}")

        for (i in minLag until maxLag) {
            if (autocorrelation[i] > threshold &&
                autocorrelation[i] > autocorrelation[i-1] &&
                autocorrelation[i] > autocorrelation[i+1]) {

                peaks.add(i)
                Log.d(TAG, "Пик автокорреляции: x=$i, y=${"%.2f".format(autocorrelation[i])}")
            }
        }

        return peaks
    }

    /**
     * Упрощенный метод расчета пульса при завершении измерения
     */
    private fun calculateHeartRate() {
        if (redChannelValues.size < MOVING_WINDOW_SIZE * 2) {
            runOnUiThread {
                binding.pulseRateText.text = "Недостаточно данных"
                Toast.makeText(this, "Недостаточно данных для определения пульса", Toast.LENGTH_LONG).show()
            }
            return
        }

        // Напрямую используем только красный канал без фильтрации
        val heartRate = getHeartRateFromPeaks(redChannelValues, timeValues)

        runOnUiThread {
            if (heartRate > 0) {
                lastValidHeartRate = heartRate // Сохраняем валидное значение
                heartRateConfidence = 1.0 // Устанавливаем максимальное доверие
                binding.pulseRateText.text = "$heartRate уд/мин"
            } else {
                // Используем последнее валидное значение, если оно есть
                binding.pulseRateText.text = "$lastValidHeartRate уд/мин (примерно)"
                Toast.makeText(this, "Точное определение пульса не удалось, показано приблизительное значение", Toast.LENGTH_LONG).show()
            }
        }
    }

    private fun recordManualPulse() {
        // Записываем текущее время
        val currentTime = System.currentTimeMillis()
        manualPulseTimestamps.add(currentTime)

        // Вибрация для обратной связи
        val vibrator = getSystemService(VIBRATOR_SERVICE) as android.os.Vibrator
        if (android.os.Build.VERSION.SDK_INT >= android.os.Build.VERSION_CODES.O) {
            vibrator.vibrate(android.os.VibrationEffect.createOneShot(50, android.os.VibrationEffect.DEFAULT_AMPLITUDE))
        } else {
            @Suppress("DEPRECATION")
            vibrator.vibrate(50)
        }

        // Обновляем пульс после добавления новой метки
        if (manualPulseTimestamps.size >= 2) {
            updateManualHeartRate()
        }
    }

    private fun updateManualHeartRate() {
        if (manualPulseTimestamps.size < 2) return

        // Вычисляем средний интервал между ударами
        val intervals = mutableListOf<Long>()
        for (i in 1 until manualPulseTimestamps.size) {
            intervals.add(manualPulseTimestamps[i] - manualPulseTimestamps[i-1])
        }

        // Используем медиану для устойчивости к выбросам
        intervals.sort()
        val medianInterval = intervals[intervals.size / 2]

        // Вычисляем пульс в ударах в минуту
        val bpm = (60.0 * 1000.0 / medianInterval).toInt()

        // Проверяем на разумные пределы
        manualHeartRate = if (bpm in MIN_VALID_HEART_RATE..MAX_VALID_HEART_RATE) bpm else 0

        // Обновляем доверие к ручному измерению (чем больше данных, тем выше доверие)
        manualHeartRateConfidence = minOf(1.0, manualPulseTimestamps.size / 10.0)

        runOnUiThread {
            if (manualHeartRate > 0) {
                binding.manualPulseText.text = "$manualHeartRate уд/мин (ручной)"
            }
        }
    }

    /**
     * Показывает диагностическую информацию о качестве сигнала
     */
    private fun showSignalQualityDiagnostics() {
        if (redChannelValues.size < 5) {
            Toast.makeText(this, "Недостаточно данных для диагностики", Toast.LENGTH_SHORT).show()
            return
        }

        // Берем последние значения для анализа
        val lastRedValues = redChannelValues.takeLast(5)
        val lastGreenValues = greenChannelValues.takeLast(5)
        val lastBlueValues = blueChannelValues.takeLast(5)

        // Вычисляем среднюю яркость для каждого канала
        val avgRed = lastRedValues.average()
        val avgGreen = lastGreenValues.average()
        val avgBlue = lastBlueValues.average()

        // Общая яркость
        val brightness = avgRed * 0.5 + avgGreen * 0.3 + avgBlue * 0.2

        // Проверка отношения красного канала к другим
        val redToGreenRatio = avgRed / (avgGreen + 1.0)
        val redToBlueRatio = avgRed / (avgBlue + 1.0)

        // Вариация в красном канале
        val redVariation = if (lastRedValues.size > 3) {
            lastRedValues.maxOrNull()!! - lastRedValues.minOrNull()!!
        } else {
            0.0
        }

        // Логирование подробной диагностической информации
        Log.i(TAG, """
            Диагностика:
            Размер данных: ${redChannelValues.size}
            Яркость: ${"%.1f".format(brightness)}
            Красный: ${"%.1f".format(avgRed)}
            Зеленый: ${"%.1f".format(avgGreen)}
            Синий: ${"%.1f".format(avgBlue)}
            Отношение Кр/Зел: ${"%.2f".format(redToGreenRatio)}
            Отношение Кр/Син: ${"%.2f".format(redToBlueRatio)}
            Вариация красного: ${"%.2f".format(redVariation)}
            Качество сигнала: ${(signalQuality * 100).toInt()}%
        """.trimIndent())

        // Результаты диагностики
        val diagnosticInfo = """
            Диагностика качества сигнала:
            
            Яркость: ${"%.1f".format(brightness)}
            Красный: ${"%.1f".format(avgRed)}
            Зеленый: ${"%.1f".format(avgGreen)}
            Синий: ${"%.1f".format(avgBlue)}
            
            Отношение Кр/Зел: ${"%.2f".format(redToGreenRatio)}
            Отношение Кр/Син: ${"%.2f".format(redToBlueRatio)}
            
            Вариация красного: ${"%.2f".format(redVariation)}
            
            Качество сигнала: ${(signalQuality * 100).toInt()}%
        """.trimIndent()

        // Показываем диалог с информацией
        androidx.appcompat.app.AlertDialog.Builder(this)
            .setTitle("Диагностика")
            .setMessage(diagnosticInfo)
            .setPositiveButton("ОК") { dialog, _ -> dialog.dismiss() }
            .show()
    }

    // Метод для включения/выключения записи данных для отладки
    private fun toggleDataRecording() {
        // Проверяем разрешения для записи
        if (checkStoragePermissions()) {
            isRecordingData = !isRecordingData

            if (isRecordingData) {
                // Начинаем запись данных
                recordedData.clear()
                recordedData.append("time,red,green,blue,quality\n")
                Toast.makeText(this, "Запись данных началась", Toast.LENGTH_SHORT).show()
                Log.d(TAG, "Запись данных сигнала началась")
            } else {
                // Останавливаем запись и сохраняем данные
                if (recordedData.isNotEmpty()) {
                    saveRecordedData()
                }
            }
        } else {
            Toast.makeText(this, "Необходимо разрешение для сохранения данных", Toast.LENGTH_SHORT).show()
        }
    }

    // Проверка разрешений для работы с файлами
    private fun checkStoragePermissions(): Boolean {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            // Для Android 11+ (API 30+)
            return Environment.isExternalStorageManager()
        } else if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            // Для Android 6+ (API 23+)
            val writePermission = ContextCompat.checkSelfPermission(
                this,
                Manifest.permission.WRITE_EXTERNAL_STORAGE
            ) == PackageManager.PERMISSION_GRANTED

            if (!writePermission) {
                ActivityCompat.requestPermissions(
                    this,
                    arrayOf(Manifest.permission.WRITE_EXTERNAL_STORAGE),
                    REQUEST_STORAGE_PERMISSION
                )
                return false
            }
            return true
        }
        // До Android 6 разрешения предоставлялись при установке
        return true
    }

    // Сохранение записанных данных в файл
    private fun saveRecordedData() {
        try {
            val timestamp = SimpleDateFormat("yyyyMMdd_HHmmss", Locale.getDefault()).format(Date())
            val filename = "pulse_data_$timestamp.csv"

            // Сохраняем во внешнее хранилище в директории Documents
            val downloadsDir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOCUMENTS)
            if (!downloadsDir.exists()) {
                downloadsDir.mkdirs()
            }

            val file = File(downloadsDir, filename)
            val writer = FileWriter(file)
            writer.append(recordedData.toString())
            writer.flush()
            writer.close()

            Log.i(TAG, "Данные сохранены в файл: ${file.absolutePath}")
            Toast.makeText(this, "Данные сохранены в ${file.name}", Toast.LENGTH_LONG).show()

            // Делаем файл видимым в галерее
            MediaScannerConnection.scanFile(this, arrayOf(file.absolutePath), null, null)

        } catch (e: Exception) {
            Log.e(TAG, "Ошибка при сохранении данных: ${e.message}")
            Toast.makeText(this, "Ошибка при сохранении данных", Toast.LENGTH_SHORT).show()
        }
    }

    override fun surfaceCreated(holder: SurfaceHolder) {
        Log.d(TAG, "Surface created")
    }

    override fun surfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
        Log.d(TAG, "Surface changed")
    }

    override fun surfaceDestroyed(holder: SurfaceHolder) {
        stopHeartRateReading()
    }

    override fun onPause() {
        super.onPause()
        stopHeartRateReading()
        manualHeartRateHandler.removeCallbacks(manualHeartRateRunnable)

        // Сохраняем данные, если запись была активна
        if (isRecordingData && recordedData.isNotEmpty()) {
            saveRecordedData()
            isRecordingData = false
        }
    }

    override fun onResume() {
        super.onResume()
        manualHeartRateHandler.post(manualHeartRateRunnable)
    }
}
