"""
PROYECTO 21: FISCALIZACIÓN Y REGISTRO DE TRÁFICO EN PUERTOS MARÍTIMOS
Aplicación web (Streamlit)

Ejecutar:
    pip install -r requirements.txt
    streamlit run app.py

Coloca dataset_puertos_15000.csv en la misma carpeta que este archivo
(si no está, la app te permite subirlo desde el navegador).

Desarrollo asistido por IA: el diseño, la estructura y el desarrollo de esta
interfaz web se realizaron con la ayuda de Claude (Anthropic) como asistente
de programación.
"""
import base64
import csv
import hashlib
import hmac
import html
import io
import json
import math
import random
import re
import secrets
import threading
import time
from datetime import datetime
from pathlib import Path

import altair as alt
import pandas as pd
import streamlit as st

NOMBRE_CSV = "dataset_puertos_15000.csv"
TOTAL_ESPERADO = 15000
LIMITE_HISTORIAL = 1000
ARCHIVO_USUARIOS = Path(__file__).resolve().parent / "usuarios.json"
ITERACIONES_HASH = 200_000
ARCHIVO_ACCESOS = Path(__file__).resolve().parent / "accesos.json"
LIMITE_ACCESOS = 5000
ARCHIVO_ALFA_GENERAL = Path(__file__).resolve().parent / "alfa_general.json"
MUESTRA_ANIMACION = 12            # datos que se usan en la animación del ordenamiento

# --- Textos de la interfaz (edítalos) ---
TITULO_PROYECTO = "Proyecto 21: Fiscalización y Registro de Tráfico en Puertos Marítimos"
CREDITOS_ALUMNOS = "Nombre de los alumnos desarrolladores"      # <- pon aquí los nombres
CREDITOS_IA = "IA utilizada: Claude (Anthropic)"


# =============================================================================
# 1. Clase del modelo (Orientada a Objetos)
# =============================================================================
class RegistroPortuario:
    def __init__(self, id_contenedor_teu, peso_bruto_kg, fecha_atracadero, puerto_operacion,
                 linea_naviera, estado, municipio, tipo_carga, estatus_aduanal, costo_maniobra_usd):
        # Campos Clave (Numéricos enteros estrictos)
        self.id_contenedor_teu = int(id_contenedor_teu)
        self.peso_bruto_kg = int(peso_bruto_kg)
        self.fecha_atracadero = int(fecha_atracadero)

        # Campos Informativos (Textos y flotante)
        self.puerto_operacion = str(puerto_operacion)
        self.linea_naviera = str(linea_naviera)
        self.estado = str(estado)
        self.municipio = str(municipio)
        self.tipo_carga = str(tipo_carga)
        self.estatus_aduanal = str(estatus_aduanal)
        self.costo_maniobra_usd = float(costo_maniobra_usd)


CAMPOS_CLAVE = ["id_contenedor_teu", "peso_bruto_kg", "fecha_atracadero"]
TODOS_LOS_CAMPOS = CAMPOS_CLAVE + [
    "puerto_operacion", "linea_naviera", "estado", "municipio",
    "tipo_carga", "estatus_aduanal", "costo_maniobra_usd",
]


# =============================================================================
# 2. Carga a la memoria RAM con benchmarking
# =============================================================================
def cargar_datos_en_ram(fuente):
    """fuente: ruta (str/Path) o archivo subido por Streamlit (UploadedFile)."""
    lista_registros = []

    tiempo_inicio = time.perf_counter_ns()

    if hasattr(fuente, "getvalue"):
        archivo_csv = io.StringIO(fuente.getvalue().decode("utf-8-sig"))
    else:
        archivo_csv = open(fuente, mode="r", encoding="utf-8-sig", newline="")

    with archivo_csv:
        lector = csv.DictReader(archivo_csv)
        faltantes = [c for c in TODOS_LOS_CAMPOS if c not in (lector.fieldnames or [])]
        if faltantes:
            raise ValueError("Al CSV le faltan estas columnas: " + ", ".join(faltantes))
        for fila in lector:
            lista_registros.append(RegistroPortuario(
                fila["id_contenedor_teu"],
                fila["peso_bruto_kg"],
                fila["fecha_atracadero"],
                fila["puerto_operacion"],
                fila["linea_naviera"],
                fila["estado"],
                fila["municipio"],
                fila["tipo_carga"],
                fila["estatus_aduanal"],
                fila["costo_maniobra_usd"],
            ))

    tiempo_total_ns = time.perf_counter_ns() - tiempo_inicio
    return lista_registros, tiempo_total_ns


# =============================================================================
# 3. FASE DE ORDENACIÓN
# -----------------------------------------------------------------------------
# Convención de las métricas (igual en los tres algoritmos):
#   - Comparaciones: +1 cada vez que se evalúa una condición entre valores.
#   - Intercambios/Movimientos: +1 por cada objeto que se escribe/reasigna en
#     una posición de un arreglo. Un swap cuenta como 2 (reubica dos objetos).
#   - Tiempo: time.perf_counter_ns() alrededor de toda la ordenación (incluye
#     el costo de mantener los contadores).
# Cada algoritmo modifica directamente la lista recibida y retorna
# (tiempo_ns, comparaciones, movimientos).
# =============================================================================
class Contador:
    __slots__ = ("comparaciones", "movimientos")

    def __init__(self):
        self.comparaciones = 0
        self.movimientos = 0


# ---------- Radix Sort (LSD, base 10) por id_contenedor_teu ----------
def radix_sort_id(registros):
    c = Contador()
    n = len(registros)
    inicio = time.perf_counter_ns()

    max_val = registros[0].id_contenedor_teu
    for reg in registros[1:]:
        c.comparaciones += 1
        if reg.id_contenedor_teu > max_val:
            max_val = reg.id_contenedor_teu

    exp = 1
    while True:
        c.comparaciones += 1                      # control: ¿quedan dígitos?
        if max_val // exp <= 0:
            break

        # Counting Sort estable por el dígito actual
        conteo = [0] * 10
        for reg in registros:
            conteo[(reg.id_contenedor_teu // exp) % 10] += 1
        for d in range(1, 10):
            conteo[d] += conteo[d - 1]

        salida = [None] * n
        for i in range(n - 1, -1, -1):
            reg = registros[i]
            d = (reg.id_contenedor_teu // exp) % 10
            conteo[d] -= 1
            salida[conteo[d]] = reg
            c.movimientos += 1

        for i in range(n):                        # volcar a la lista original
            registros[i] = salida[i]
            c.movimientos += 1

        exp *= 10

    return time.perf_counter_ns() - inicio, c.comparaciones, c.movimientos


# ---------- Bucket Sort por peso_bruto_kg ----------
def bucket_sort_peso(registros):
    c = Contador()
    n = len(registros)
    inicio = time.perf_counter_ns()

    minimo = maximo = registros[0].peso_bruto_kg
    for reg in registros[1:]:
        p = reg.peso_bruto_kg
        c.comparaciones += 1
        if p < minimo:
            minimo = p
        c.comparaciones += 1
        if p > maximo:
            maximo = p

    num_cubos = max(1, int(math.sqrt(n)))
    rango = maximo - minimo + 1
    cubos = [[] for _ in range(num_cubos)]

    for reg in registros:                         # distribución en cubos
        idx = (reg.peso_bruto_kg - minimo) * num_cubos // rango
        cubos[idx].append(reg)
        c.movimientos += 1

    for cubo in cubos:                            # Insertion Sort por cubo (estable)
        for i in range(1, len(cubo)):
            actual = cubo[i]
            clave = actual.peso_bruto_kg
            j = i - 1
            while j >= 0:
                c.comparaciones += 1
                if cubo[j].peso_bruto_kg > clave:
                    cubo[j + 1] = cubo[j]
                    c.movimientos += 1
                    j -= 1
                else:
                    break
            if j + 1 != i:
                cubo[j + 1] = actual
                c.movimientos += 1

    pos = 0                                       # concatenar de vuelta
    for cubo in cubos:
        for reg in cubo:
            registros[pos] = reg
            c.movimientos += 1
            pos += 1

    return time.perf_counter_ns() - inicio, c.comparaciones, c.movimientos


# ---------- Quick Sort (3 vías, pivote aleatorio) por fecha_atracadero ----------
# La partición de 3 vías evita el peor caso O(n^2) con fechas repetidas y se
# recurre primero sobre la mitad menor para mantener la pila en O(log n).
def _quick_sort_rec(registros, lo, hi, c):
    while lo < hi:
        pivote = registros[random.randint(lo, hi)].fecha_atracadero
        lt, i, gt = lo, lo, hi
        while i <= gt:
            valor = registros[i].fecha_atracadero
            c.comparaciones += 1
            if valor < pivote:
                if lt != i:
                    registros[lt], registros[i] = registros[i], registros[lt]
                    c.movimientos += 2
                lt += 1
                i += 1
            else:
                c.comparaciones += 1
                if valor > pivote:
                    if i != gt:
                        registros[i], registros[gt] = registros[gt], registros[i]
                        c.movimientos += 2
                    gt -= 1
                else:
                    i += 1

        if lt - lo < hi - gt:
            _quick_sort_rec(registros, lo, lt - 1, c)
            lo = gt + 1
        else:
            _quick_sort_rec(registros, gt + 1, hi, c)
            hi = lt - 1


def quick_sort_fecha(registros):
    c = Contador()
    inicio = time.perf_counter_ns()
    _quick_sort_rec(registros, 0, len(registros) - 1, c)
    return time.perf_counter_ns() - inicio, c.comparaciones, c.movimientos


# Opción -> (campo, nombre del método, función)
MOTOR_ORDENACION = {
    1: ("id_contenedor_teu", "Radix Sort", radix_sort_id),
    2: ("peso_bruto_kg", "Bucket Sort", bucket_sort_peso),
    3: ("fecha_atracadero", "Quick Sort", quick_sort_fecha),
}
METODOS = [m[1] for m in MOTOR_ORDENACION.values()]


def esta_ordenado(registros, atributo):
    return all(getattr(registros[i], atributo) <= getattr(registros[i + 1], atributo)
               for i in range(len(registros) - 1))


# =============================================================================
# 4. FASE DE BÚSQUEDA
# =============================================================================
def busqueda_binaria(registros, campo, objetivo):
    """Requiere la lista ordenada por `campo`.

    Encuentra una coincidencia con búsqueda binaria y luego se expande hacia la
    izquierda y la derecha (los valores repetidos quedan contiguos al estar
    ordenada la lista). Retorna (lista_de_posiciones, ns, pasos).
    """
    inicio = time.perf_counter_ns()
    lo, hi = 0, len(registros) - 1
    encontrado, pasos = -1, 0
    while lo <= hi:
        pasos += 1
        medio = (lo + hi) // 2
        valor = getattr(registros[medio], campo)
        if valor == objetivo:
            encontrado = medio
            break
        if valor < objetivo:
            lo = medio + 1
        else:
            hi = medio - 1

    posiciones = []
    if encontrado >= 0:
        izq = encontrado
        while izq - 1 >= 0 and getattr(registros[izq - 1], campo) == objetivo:
            pasos += 1
            izq -= 1
        der = encontrado
        while der + 1 < len(registros) and getattr(registros[der + 1], campo) == objetivo:
            pasos += 1
            der += 1
        posiciones = list(range(izq, der + 1))
    return posiciones, time.perf_counter_ns() - inicio, pasos


def busqueda_lineal(registros, campo, objetivo):
    """Recorrido secuencial completo sobre cualquier campo.
    Retorna (lista_de_posiciones, ns, pasos)."""
    inicio = time.perf_counter_ns()
    posiciones, pasos = [], 0
    for i, reg in enumerate(registros):
        pasos += 1
        if getattr(reg, campo) == objetivo:
            posiciones.append(i)
    return posiciones, time.perf_counter_ns() - inicio, pasos


def convertir_valor(campo, texto):
    """Convierte lo escrito por el usuario al tipo del campo. Lanza ValueError si no es válido."""
    texto = texto.strip()
    if campo in CAMPOS_CLAVE:
        if not (texto.isascii() and texto.isdigit()):
            raise ValueError(f"{campo} debe ser un número entero (solo dígitos).")
        return int(texto)
    if campo == "costo_maniobra_usd":
        try:
            return float(texto)
        except ValueError:
            raise ValueError("El costo debe ser un número (por ejemplo 1234.56).") from None
    if not texto:
        raise ValueError("Escribe el valor que quieres buscar.")
    return texto




# =============================================================================
# 4b. Cuentas de usuario y registro de accesos
# -----------------------------------------------------------------------------
# Las cuentas se guardan en usuarios.json junto a app.py. La clave es opcional:
# si existe, solo se guarda un hash PBKDF2-SHA256 con sal aleatoria (nunca la
# clave en texto plano). Una cuenta sin clave entra solo con su nombre.
# =============================================================================
PATRON_USUARIO = re.compile(r"[A-Za-z0-9_.-]{3,30}")
LARGO_MINIMO_CLAVE = 6


def ahora():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


@st.cache_resource
def _candado_usuarios():
    return threading.Lock()


def _guardar_json(ruta, datos):
    """Escritura atómica. Retorna False si el servidor no permite escribir."""
    try:
        temporal = ruta.with_suffix(".tmp")
        temporal.write_text(json.dumps(datos, ensure_ascii=False, indent=1), encoding="utf-8")
        temporal.replace(ruta)
        return True
    except OSError:
        return False


def _leer_usuarios():
    try:
        datos = json.loads(ARCHIVO_USUARIOS.read_text(encoding="utf-8"))
        return datos if isinstance(datos, dict) else {}
    except (OSError, ValueError):
        return {}


def _hash_contrasena(contrasena, sal):
    return hashlib.pbkdf2_hmac("sha256", contrasena.encode("utf-8"), sal,
                               ITERACIONES_HASH).hex()


def _clave_correcta(registro, clave):
    return hmac.compare_digest(
        _hash_contrasena(clave, bytes.fromhex(registro["sal"])), registro["hash"])


def acceder(usuario, clave, sin_clave):
    """Registra la cuenta si es nueva o inicia sesión si ya existe.

    Retorna (nombre, error): nombre es None cuando no se pudo entrar.
    """
    usuario = usuario.strip()
    if not PATRON_USUARIO.fullmatch(usuario):
        return None, ("El nombre de usuario debe tener de 3 a 30 caracteres: "
                      "letras, números, _ . -")
    sin_clave = sin_clave or not clave

    nueva = False
    with _candado_usuarios():
        usuarios = _leer_usuarios()
        registro = usuarios.get(usuario.lower())
        if registro is None:                                   # cuenta nueva
            if not sin_clave and len(clave) < LARGO_MINIMO_CLAVE:
                return None, (f"La clave debe tener al menos {LARGO_MINIMO_CLAVE} caracteres "
                              "(o usa «Ingresar sin clave»).")
            sal = secrets.token_bytes(16)
            usuarios[usuario.lower()] = {
                "nombre": usuario,
                "sal": None if sin_clave else sal.hex(),
                "hash": None if sin_clave else _hash_contrasena(clave, sal),
                "creado": ahora(),
            }
            if not _guardar_json(ARCHIVO_USUARIOS, usuarios):
                return None, "No se pudo guardar la cuenta (el servidor no permite escribir)."
            nueva = True

    if nueva:
        registrar_acceso(usuario, "Cuenta creada")
        registrar_acceso(usuario, "Inicio de sesión")
        return usuario, None

    if registro.get("hash"):                                   # la cuenta tiene clave
        if sin_clave:
            registrar_acceso(registro["nombre"], "Intento fallido")
            return None, "Ese usuario tiene clave: escríbela para entrar."
        if not _clave_correcta(registro, clave):
            registrar_acceso(registro["nombre"], "Intento fallido")
            return None, "Usuario o clave incorrectos."
    registrar_acceso(registro["nombre"], "Inicio de sesión")
    return registro["nombre"], None


def cuenta_tiene_clave(usuario):
    return bool(_leer_usuarios().get(usuario.lower(), {}).get("hash"))


def cambiar_clave(usuario, actual, nueva):
    """Pone, cambia o quita (nueva vacía) la clave. Retorna (ok, mensaje)."""
    if nueva and len(nueva) < LARGO_MINIMO_CLAVE:
        return False, f"La clave nueva debe tener al menos {LARGO_MINIMO_CLAVE} caracteres."
    with _candado_usuarios():
        usuarios = _leer_usuarios()
        registro = usuarios.get(usuario.lower())
        if registro is None:
            return False, "La cuenta ya no existe."
        if registro.get("hash") and not (actual and _clave_correcta(registro, actual)):
            return False, "La clave actual no es correcta."
        if nueva:
            sal = secrets.token_bytes(16)
            registro["sal"], registro["hash"] = sal.hex(), _hash_contrasena(nueva, sal)
        else:
            registro["sal"], registro["hash"] = None, None
        if not _guardar_json(ARCHIVO_USUARIOS, usuarios):
            return False, "No se pudo guardar el cambio (el servidor no permite escribir)."
    return True, ("Clave actualizada." if nueva
                  else "Clave eliminada: ahora esta cuenta entra sin clave.")


@st.cache_resource
def _accesos():
    """Registro de accesos compartido por todas las sesiones y guardado en accesos.json."""
    try:
        filas = json.loads(ARCHIVO_ACCESOS.read_text(encoding="utf-8"))
        return filas if isinstance(filas, list) else []
    except (OSError, ValueError):
        return []


def registrar_acceso(usuario, evento):
    """Agrega una fila (hora, usuario, evento) al registro de accesos."""
    with _candado_usuarios():
        filas = _accesos()
        filas.append({"Hora": ahora(), "Usuario": usuario, "Evento": evento})
        del filas[:-LIMITE_ACCESOS]
        _guardar_json(ARCHIVO_ACCESOS, filas)      # si falla, queda solo en memoria


def resumen_por_persona():
    """Una fila por cuenta: cuándo se creó, cuántas veces entró y su último acceso."""
    entradas = {}
    for fila in list(_accesos()):
        if fila["Evento"] == "Inicio de sesión":
            n, _ = entradas.get(fila["Usuario"].lower(), (0, ""))
            entradas[fila["Usuario"].lower()] = (n + 1, fila["Hora"])
    return [{
        "Usuario": datos["nombre"],
        "Clave": "Sí" if datos.get("hash") else "No",
        "Cuenta creada": datos.get("creado"),
        "Veces que entró": entradas.get(clave, (0, None))[0],
        "Último acceso": entradas.get(clave, (0, None))[1],
    } for clave, datos in _leer_usuarios().items()]


def cerrar_sesion():
    registrar_acceso(st.session_state.get("usuario", "?"), "Cierre de sesión")
    st.session_state.clear()     # también reinicia el Método Alfa de esta sesión


# =============================================================================
# 5. Método Alfa: del usuario (por sesión) y general (acumulado de todos)
# -----------------------------------------------------------------------------
# - Alfa del usuario: vive en st.session_state; empieza en 0 cada vez que la
#   persona entra y se puede reiniciar sin afectar al general.
# - Alfa general: acumulado global de todas las personas, guardado en
#   alfa_general.json; el reinicio del usuario no lo modifica.
# =============================================================================
def _stats_vacias():
    return {"veces": 0, "ns_total": 0, "comparaciones_total": 0, "movimientos_total": 0}


def obtener_bitacora():
    if "bitacora" not in st.session_state:
        st.session_state.bitacora = {
            "datos": {
                "rondas": 0,
                "metodos": {m: _stats_vacias() for m in METODOS},
                "historial": [],
            },
            "lock": threading.Lock(),
        }
    return st.session_state.bitacora


@st.cache_resource
def obtener_general():
    datos = {"rondas": 0, "metodos": {m: _stats_vacias() for m in METODOS}}
    try:
        guardado = json.loads(ARCHIVO_ALFA_GENERAL.read_text(encoding="utf-8"))
        datos["rondas"] = int(guardado.get("rondas", 0))
        for m in METODOS:
            datos["metodos"][m].update(guardado.get("metodos", {}).get(m, {}))
    except (OSError, ValueError, AttributeError):
        pass                                       # primera ejecución o archivo dañado
    return {"datos": datos, "lock": threading.Lock()}


def _agregar_evento(datos, evento):
    fila = {"Hora": ahora(), **evento}
    datos["historial"].append(fila)
    del datos["historial"][:-LIMITE_HISTORIAL]


def _sumar_ronda(datos, metodo, ns, comparaciones, movimientos):
    stats = datos["metodos"][metodo]
    stats["veces"] += 1
    stats["ns_total"] += ns
    stats["comparaciones_total"] += comparaciones
    stats["movimientos_total"] += movimientos
    datos["rondas"] += 1


def registrar_ronda(campo, metodo, ns, comparaciones, movimientos):
    bit = obtener_bitacora()
    with bit["lock"]:
        _sumar_ronda(bit["datos"], metodo, ns, comparaciones, movimientos)
        _agregar_evento(bit["datos"], {
            "Evento": "Ordenación", "Método / tipo": metodo, "Campo": campo,
            "Valor buscado": None, "Resultado": f"Lista ordenada por {campo}",
            "Tiempo (ns)": ns, "Comparaciones": comparaciones,
            "Movimientos": movimientos, "Pasos": None,
        })
    general = obtener_general()
    with general["lock"]:
        _sumar_ronda(general["datos"], metodo, ns, comparaciones, movimientos)
        _guardar_json(ARCHIVO_ALFA_GENERAL, general["datos"])


def registrar_busqueda(tipo, campo, objetivo, posiciones, ns, pasos):
    bit = obtener_bitacora()
    with bit["lock"]:
        _agregar_evento(bit["datos"], {
            "Evento": "Búsqueda", "Método / tipo": tipo, "Campo": campo,
            "Valor buscado": str(objetivo),
            "Resultado": (f"{len(posiciones):,} coincidencia(s); primera en la posición "
                          f"{posiciones[0] + 1:,}" if posiciones else "No encontrado"),
            "Tiempo (ns)": ns, "Comparaciones": None, "Movimientos": None, "Pasos": pasos,
        })


def reiniciar_alfa_usuario():
    """Deja en 0 el Método Alfa de esta persona. No toca el Alfa general."""
    bit = obtener_bitacora()
    with bit["lock"]:
        bit["datos"]["rondas"] = 0
        bit["datos"]["metodos"] = {m: _stats_vacias() for m in METODOS}


def calcular_alfa(metodos):
    """Retorna (alfa por frecuencia, alfa por rendimiento) como listas de nombres.

    - Frecuencia: el método seleccionado más veces.
    - Rendimiento: el método con menor tiempo promedio de ordenación (ns).
    Si aún no hay rondas retorna (None, None).
    """
    usados = {m: s for m, s in metodos.items() if s["veces"] > 0}
    if not usados:
        return None, None
    max_veces = max(s["veces"] for s in usados.values())
    por_frecuencia = [m for m, s in usados.items() if s["veces"] == max_veces]
    promedio = {m: s["ns_total"] / s["veces"] for m, s in usados.items()}
    mejor = min(promedio.values())
    por_rendimiento = [m for m, p in promedio.items() if p == mejor]
    return por_frecuencia, por_rendimiento


def porcentajes(metodos):
    """Porcentaje de rondas en que se seleccionó cada método."""
    total = sum(s["veces"] for s in metodos.values())
    return {m: (round(100 * s["veces"] / total) if total else 0) for m, s in metodos.items()}


# =============================================================================
# 6. Carga de datos, ordenación (disparador) y búsquedas
# =============================================================================
def valor_texto(reg, campo):
    """Valor de un campo como texto (el costo con 2 decimales)."""
    v = getattr(reg, campo)
    return f"{v:.2f}" if campo == "costo_maniobra_usd" else str(v)


def generar_txt_ordenado(registros, campo, metodo, tiempo_ns, comparaciones, movimientos):
    """Contenido del .txt descargable: resumen del benchmarking + lista ordenada."""
    lineas = [
        "PROYECTO 21: FISCALIZACIÓN Y REGISTRO DE TRÁFICO EN PUERTOS MARÍTIMOS",
        f"Se ordenaron {len(registros):,} registros por el campo {campo} usando el método "
        f"{metodo} en {tiempo_ns} nanosegundos. Comparaciones: {comparaciones}, "
        f"Intercambios/Movimientos: {movimientos}",
        "",
        " | ".join(TODOS_LOS_CAMPOS),
    ]
    for reg in registros:
        lineas.append(" | ".join(valor_texto(reg, c) for c in TODOS_LOS_CAMPOS))
    return "\n".join(lineas) + "\n"


def cargar_fuente(fuente, nombre, tamano, origen):
    """Carga un CSV/TXT a la RAM y reinicia el estado que depende de los datos.
    Lanza ValueError / KeyError / UnicodeDecodeError / OSError si el archivo no sirve."""
    registros, tiempo_carga = cargar_datos_en_ram(fuente)
    if not registros:
        raise ValueError("El archivo no contiene registros.")
    st.session_state.registros_base = registros
    st.session_state.tiempo_carga = tiempo_carga
    st.session_state.archivo = {"nombre": nombre, "tamano": tamano, "origen": origen}
    for clave in ("resultado", "comparativo", "animar", "busq_tipo", "busq_campo"):
        st.session_state.pop(clave, None)
    st.session_state.ultima_busqueda = None


def ejecutar_ronda():
    # Cada ronda parte del orden original de los datos cargados
    base = st.session_state.registros_base
    registros_ram = list(base)

    # Disparador aleatorio de ordenación (el campo determina el método)
    opcion = random.randint(1, 3)
    campo, metodo, funcion_orden = MOTOR_ORDENACION[opcion]
    tiempo_ns, comparaciones, movimientos = funcion_orden(registros_ram)

    # Verificación de correctitud (fuera de la medición)
    if not esta_ordenado(registros_ram, campo):
        raise RuntimeError(f"La lista no quedó ordenada por {campo}")

    # Método Alfa (usuario y general) + bitácora de la sesión
    registrar_ronda(campo, metodo, tiempo_ns, comparaciones, movimientos)

    muestra = random.sample(base, min(MUESTRA_ANIMACION, len(base)))
    st.session_state.resultado = {
        "registros_ordenados": registros_ram,
        "campo": campo, "metodo": metodo,
        "ns_orden": tiempo_ns, "comparaciones": comparaciones, "movimientos": movimientos,
        "txt": generar_txt_ordenado(registros_ram, campo, metodo, tiempo_ns,
                                    comparaciones, movimientos),
        "muestra": [getattr(r, campo) for r in muestra],
    }
    st.session_state.animar = True
    # La lista cambió de orden: la búsqueda anterior ya no aplica
    st.session_state.ultima_busqueda = None
    st.session_state.pop("busq_tipo", None)
    st.session_state.pop("busq_campo", None)


def medir_comparativo():
    """Ordena una copia de los datos por cada campo clave con su algoritmo.
    No afecta al Método Alfa: es solo para el análisis comparativo."""
    filas = []
    for campo, metodo, funcion in MOTOR_ORDENACION.values():
        copia = list(st.session_state.registros_base)
        ns, comparaciones, movimientos = funcion(copia)
        filas.append({"campo": campo, "metodo": metodo, "ns": ns,
                      "comparaciones": comparaciones, "movimientos": movimientos})
    st.session_state.comparativo = filas


def disparador_busqueda():
    """Elige al azar el tipo de búsqueda; luego se pide el dato (y el campo si es lineal)."""
    res = st.session_state.get("resultado")
    tipo = random.choice(["Binaria", "Lineal"]) if res else "Lineal"
    st.session_state.busq_tipo = tipo
    # Lineal: el usuario elige cualquiera de los 10 campos. Binaria: el campo recién ordenado.
    if tipo == "Lineal":
        st.session_state.busq_campo = TODOS_LOS_CAMPOS[0]
    else:
        st.session_state.pop("busq_campo", None)
    st.session_state.busq_valor = ""
    st.session_state.ultima_busqueda = None


def cambio_campo_busqueda():
    """Al cambiar el campo de la búsqueda lineal se limpia el dato y el resultado anterior."""
    st.session_state.busq_valor = ""
    st.session_state.ultima_busqueda = None


def ventana_busqueda(lista, campo, posiciones, ancho=11):
    """Celdas (posición, valor, ¿coincide?) alrededor de la primera coincidencia."""
    if not posiciones:
        return []
    aciertos = set(posiciones)
    inicio = max(0, min(posiciones[0] - ancho // 2, len(lista) - ancho))
    return [(inicio + i + 1, valor_texto(reg, campo), (inicio + i) in aciertos)
            for i, reg in enumerate(lista[inicio:inicio + ancho])]


def lanzar_busqueda():
    """Ejecuta la búsqueda con el tipo, el campo y el dato que escribió el usuario."""
    res = st.session_state.get("resultado")
    tipo = st.session_state.get("busq_tipo")
    if tipo is None:
        st.session_state.ultima_busqueda = {
            "error": "Primero presiona «Ejecutar búsqueda»."}
        return
    if tipo == "Binaria":
        if res is None:
            st.session_state.ultima_busqueda = {
                "error": "La búsqueda binaria necesita la lista ordenada. "
                         "Primero ejecuta la ordenación."}
            return
        lista, campo = res["registros_ordenados"], res["campo"]
    else:
        lista = res["registros_ordenados"] if res else st.session_state.registros_base
        campo = st.session_state.get("busq_campo", TODOS_LOS_CAMPOS[0])

    try:
        objetivo = convertir_valor(campo, st.session_state.get("busq_valor", ""))
    except ValueError as e:
        st.session_state.ultima_busqueda = {"error": str(e)}
        return

    if tipo == "Binaria":
        posiciones, ns, pasos = busqueda_binaria(lista, campo, objetivo)
    else:
        posiciones, ns, pasos = busqueda_lineal(lista, campo, objetivo)

    registrar_busqueda(tipo, campo, objetivo, posiciones, ns, pasos)
    st.session_state.ultima_busqueda = {
        "tipo": tipo, "campo": campo, "objetivo": objetivo,
        "posiciones": posiciones, "ns": ns, "pasos": pasos,
        "registros": [lista[p] for p in posiciones],
        "ventana": ventana_busqueda(lista, campo, posiciones),
        "orden": res["campo"] if res else None,
    }


def ir_a(pagina):
    st.session_state.pagina = pagina


# -----------------------------------------------------------------------------
# Trazas didácticas: cuadros intermedios de una muestra pequeña para la animación.
# (La medición real de tiempos usa los algoritmos de la sección 3, no estas trazas.)
# -----------------------------------------------------------------------------
def trazas_ordenamiento(metodo, valores):
    """Lista de (valores, posiciones_activas) que muestra cómo avanza el algoritmo."""
    a = list(valores)
    cuadros = [(list(a), ())]
    if metodo == "Radix Sort":
        exp = 1
        while max(a) // exp > 0:
            a = [v for d in range(10) for v in a if (v // exp) % 10 == d]
            cuadros.append((list(a), ()))
            exp *= 10
    elif metodo == "Bucket Sort":
        k = max(1, int(math.sqrt(len(a))))
        minimo, rango = min(a), max(a) - min(a) + 1
        cubos = [[] for _ in range(k)]
        for v in a:
            cubos[(v - minimo) * k // rango].append(v)
        a = [v for cubo in cubos for v in cubo]
        cuadros.append((list(a), ()))
        pos = 0
        for cubo in cubos:
            if cubo:
                a[pos:pos + len(cubo)] = sorted(cubo)
                cuadros.append((list(a), tuple(range(pos, pos + len(cubo)))))
            pos += len(cubo)
    else:                                                      # Quick Sort (3 vías)
        def rec(lo, hi):
            if lo >= hi:
                return
            pivote = a[random.randint(lo, hi)]
            tramo = a[lo:hi + 1]
            menores = [v for v in tramo if v < pivote]
            iguales = [v for v in tramo if v == pivote]
            mayores = [v for v in tramo if v > pivote]
            a[lo:hi + 1] = menores + iguales + mayores
            ini = lo + len(menores)
            cuadros.append((list(a), tuple(range(ini, ini + len(iguales)))))
            rec(lo, ini - 1)
            rec(ini + len(iguales), hi)
        rec(0, len(a) - 1)
    return cuadros


# =============================================================================
# 7. Utilidades de interfaz
# =============================================================================
def a_dataframe(registros, inicio_indice):
    df = pd.DataFrame([vars(r) for r in registros])
    df.index = range(inicio_indice, inicio_indice + len(df))
    return df


# Encabezados y formato amigables para las tablas (los nombres internos no cambian)
COLUMNAS = {
    "id_contenedor_teu": st.column_config.NumberColumn("ID contenedor TEU", format="%d"),
    "peso_bruto_kg": st.column_config.NumberColumn("Peso bruto (kg)", format="%d"),
    "fecha_atracadero": st.column_config.NumberColumn("Fecha atracadero (AAAAMMDD)", format="%d"),
    "puerto_operacion": st.column_config.TextColumn("Puerto"),
    "linea_naviera": st.column_config.TextColumn("Línea naviera"),
    "estado": st.column_config.TextColumn("Estado"),
    "municipio": st.column_config.TextColumn("Municipio"),
    "tipo_carga": st.column_config.TextColumn("Tipo de carga"),
    "estatus_aduanal": st.column_config.TextColumn("Estatus aduanal"),
    "costo_maniobra_usd": st.column_config.NumberColumn("Costo maniobra (USD)", format="$%.2f"),
}

NOMBRES_CAMPOS = {
    "id_contenedor_teu": "ID contenedor TEU",
    "peso_bruto_kg": "Peso bruto (kg)",
    "fecha_atracadero": "Fecha atracadero",
    "puerto_operacion": "Puerto",
    "linea_naviera": "Línea naviera",
    "estado": "Estado",
    "municipio": "Municipio",
    "tipo_carga": "Tipo de carga",
    "estatus_aduanal": "Estatus aduanal",
    "costo_maniobra_usd": "Costo maniobra (USD)",
}

DESCRIPCIONES = {
    "id_contenedor_teu": "Identificador único del contenedor (TEU)",
    "peso_bruto_kg": "Peso bruto de la carga en kilogramos",
    "fecha_atracadero": "Fecha de atraque en el puerto (AAAAMMDD)",
    "puerto_operacion": "Puerto donde se realiza la operación",
    "linea_naviera": "Compañía naviera responsable",
    "estado": "Entidad federativa del puerto",
    "municipio": "Municipio del puerto",
    "tipo_carga": "Clasificación de la carga",
    "estatus_aduanal": "Situación del trámite aduanal",
    "costo_maniobra_usd": "Costo de la maniobra en dólares (USD)",
}

# Un color distinto por método de ordenamiento
COLORES_METODOS = {
    "Radix Sort": "#9BF00B",    # verde Xbox
    "Bucket Sort": "#F5A524",   # ámbar
    "Quick Sort": "#D9D9D9",    # gris claro
}

OPCIONES_CANTIDAD = [10, 20, 30, 50, 100]
MENU = [
    ("intro", "🏠", "Introducción del proyecto"),
    ("carga", "🗄️", "Carga de Datos"),
    ("orden", "↕️", "Ordenación"),
    ("busqueda", "🔍", "Búsqueda"),
    ("reportes", "📊", "Reportes"),
    ("alfa", "⭐", "Método Alfa"),
    ("fuentes", "📖", "Fuentes"),
]


def esc(texto):
    return html.escape(str(texto))


def uri_svg(svg):
    return "data:image/svg+xml;base64," + base64.b64encode(svg.encode("utf-8")).decode("ascii")


SVG_ARBOL = uri_svg(
    '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 56">'
    '<g fill="#fff"><rect x="24" y="2" width="16" height="13" rx="3"/>'
    '<rect x="3" y="39" width="16" height="13" rx="3"/><rect x="24" y="39" width="16" height="13" rx="3"/>'
    '<rect x="45" y="39" width="16" height="13" rx="3"/></g>'
    '<g stroke="#fff" stroke-width="3" fill="none"><path d="M32 15v12M11 39V27h42v12M32 27v12"/></g></svg>')

SVG_PORTADA = uri_svg(
    '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 220 200">'
    '<circle cx="110" cy="100" r="92" fill="#262626"/>'
    '<rect x="50" y="50" width="120" height="80" rx="8" fill="#161616" stroke="#9BF00B" stroke-width="6"/>'
    '<rect x="70" y="98" width="14" height="20" fill="#4C7D0A"/><rect x="92" y="86" width="14" height="32" fill="#76B80A"/>'
    '<rect x="114" y="74" width="14" height="44" fill="#9BF00B"/>'
    '<rect x="32" y="132" width="156" height="10" rx="5" fill="#9BF00B"/>'
    '<circle cx="150" cy="96" r="22" fill="#ffffff" fill-opacity="0.12" stroke="#9BF00B" stroke-width="7"/>'
    '<line x1="166" y1="113" x2="190" y2="138" stroke="#9BF00B" stroke-width="9" stroke-linecap="round"/></svg>')


def tarjeta(titulo, valor, extra="", clase=""):
    return (f'<div class="tarjeta {clase}"><div class="tt">{esc(titulo)}</div>'
            f'<div class="tv">{esc(valor)}</div>{extra}</div>')


def titulo_pagina(icono, titulo, subtitulo):
    st.markdown(
        f'<div class="titulo-pagina"><div class="ico">{icono}</div>'
        f'<div><h2>{esc(titulo)}</h2><p>{esc(subtitulo)}</p></div></div>',
        unsafe_allow_html=True)


def panel_titulo(texto):
    st.markdown(f'<div class="panel-titulo">{esc(texto)}</div>', unsafe_allow_html=True)


def html_fichas(valores):
    return '<div class="fichas">' + "".join(f'<span class="ficha">{esc(v)}</span>'
                                            for v in valores) + "</div>"


def html_barras(valores, activos=()):
    maximo = max(valores) or 1
    barras = "".join(
        f'<div class="barra{" act" if i in activos else ""}" '
        f'style="height:{max(6, int(100 * v / maximo))}%"></div>'
        for i, v in enumerate(valores))
    return f'<div class="barras">{barras}</div>'


def html_ventana(celdas):
    flechas = "".join(f'<div class="celda-f">{"▼" if hit else ""}</div>' for _, _, hit in celdas)
    valores = "".join(f'<div class="celda{" hit" if hit else ""}" title="Posición {pos}">'
                      f'{esc(valor)}</div>' for pos, valor, hit in celdas)
    return f'<div class="ventana">{flechas}</div><div class="ventana">{valores}</div>'


def html_alfa(metodos, alfa):
    pct = porcentajes(metodos)
    filas = []
    for m in sorted(METODOS, key=lambda x: -metodos[x]["veces"]):
        es_alfa = bool(alfa) and m in alfa
        etiqueta = f"{m} ★ ALFA ({pct[m]}%)" if es_alfa else f"{m} ({pct[m]}%)"
        filas.append(f'<div class="alfa-barra{" alfa" if es_alfa else ""}">'
                     f'<div class="relleno" style="width:{pct[m]}%"></div>'
                     f'<span>{esc(etiqueta)}</span></div>')
    return "".join(filas)


def cantidad_selector(clave):
    """Selector «Cantidad de registros a visualizar» (recuerda el último valor elegido)."""
    actual = st.session_state.get("cant_registros", 30)
    indice = OPCIONES_CANTIDAD.index(actual) if actual in OPCIONES_CANTIDAD else 2
    n = st.selectbox("🔢 Cantidad de registros a visualizar", OPCIONES_CANTIDAD,
                     index=indice, key=clave)
    st.session_state.cant_registros = n
    return n


def tablas_primeros_ultimos(registros, n, titulo_izq="⏮ Primeros registros",
                            titulo_der="⏭ Últimos registros"):
    izq, der = st.columns(2)
    with izq:
        panel_titulo(titulo_izq)
        st.dataframe(a_dataframe(registros[:n], 1), column_config=COLUMNAS)
    with der:
        panel_titulo(titulo_der)
        st.dataframe(a_dataframe(registros[-n:], max(len(registros) - n + 1, 1)),
                     column_config=COLUMNAS)


def requiere_datos():
    if "registros_base" in st.session_state:
        return True
    st.warning("Primero carga los datos en la opción **Carga de Datos** del menú.")
    st.button("Ir a Carga de Datos", on_click=ir_a, args=("carga",), key="ir_carga")
    return False


def formato_tamano(tamano):
    return f"{tamano / 1024:,.0f} KB" if tamano >= 1024 else f"{tamano} bytes"


def reproducir_animacion(zona, cuadros):
    pausa = min(0.45, 2.6 / max(len(cuadros), 1))
    for i, (valores, activos) in enumerate(cuadros, 1):
        zona.markdown(html_barras(valores, activos)
                      + f'<div class="pie-barras">Paso {i} de {len(cuadros)}</div>',
                      unsafe_allow_html=True)
        time.sleep(pausa)
    zona.markdown(html_barras(cuadros[-1][0])
                  + '<div class="pie-barras">✔ Ordenado</div>', unsafe_allow_html=True)


def grafica_comparativa(filas):
    """Barras horizontales con el tiempo de cada campo clave y su método."""
    df = pd.DataFrame([{
        "Campo y método": f"{NOMBRES_CAMPOS[f['campo']]} — {f['metodo']}",
        "Tiempo (ns)": f["ns"], "Método": f["metodo"]} for f in filas])
    barras = (
        alt.Chart(df)
        .mark_bar(cornerRadiusTopRight=4, cornerRadiusBottomRight=4)
        .encode(
            y=alt.Y("Campo y método:N", sort=None, title=None),
            x=alt.X("Tiempo (ns):Q", title="Tiempo de ordenación (ns)"),
            color=alt.Color("Método:N",
                            scale=alt.Scale(domain=list(COLORES_METODOS.keys()),
                                            range=list(COLORES_METODOS.values())),
                            legend=None),
            tooltip=[alt.Tooltip("Campo y método:N"), alt.Tooltip("Tiempo (ns):Q", format=",")],
        )
        .properties(height=170)
    )
    st.altair_chart(barras)


# =============================================================================
# 8. Estilo visual (maqueta del Avance 2)
# =============================================================================
ESTILO = """
<style>
:root { --verde:#9BF00B; --fondo:#161616; --negro:#050505; --panel:#1C1C1C; --borde:#3A3A3A;
        --texto:#FFFFFF; --suave:#A8A8A8; }
.stApp { background: var(--fondo); }
[data-testid="stHeader"] { background: transparent; }
.block-container { padding-top: 1.1rem; max-width: 1320px; }
#MainMenu, footer { visibility: hidden; }
[data-testid="stMain"] h1, [data-testid="stMain"] h2, [data-testid="stMain"] h3,
[data-testid="stMain"] p, [data-testid="stMain"] li, [data-testid="stMain"] label { color: var(--texto); }

/* Cabecera */
div[data-testid="stHorizontalBlock"]:has(.cabecera-marca) {
    background: var(--negro); border-radius: 14px; padding: .7rem 1.2rem; align-items: center;
    margin-bottom: 1rem; border: 1px solid var(--borde); }
.cabecera-marca { display: flex; align-items: center; gap: 1rem; }
.cabecera-marca img { width: 46px; height: 40px; }
.cabecera-marca .sep { width: 1px; height: 48px; background: rgba(255,255,255,.25); }
.cabecera-marca .t1 { font-size: 1.55rem; font-weight: 800; line-height: 1.1; color: #fff !important; }
.cabecera-marca .pill { display: inline-block; margin-top: .3rem; background: transparent;
    border: 1px solid var(--verde); color: var(--verde) !important; border-radius: 4px;
    padding: .1rem .9rem; font-weight: 800; font-size: .85rem; }
div[data-testid="stHorizontalBlock"]:has(.cabecera-marca) [data-testid="stPopover"] button,
div[data-testid="stHorizontalBlock"]:has(.cabecera-marca) [data-testid="stExpander"] summary {
    background: transparent; border: 1px solid var(--verde); border-radius: 4px; }
div[data-testid="stHorizontalBlock"]:has(.cabecera-marca) [data-testid="stPopover"] button *,
div[data-testid="stHorizontalBlock"]:has(.cabecera-marca) [data-testid="stExpander"] summary * {
    color: var(--verde) !important; font-weight: 800; }

/* Menú lateral */
[data-testid="stSidebar"] { background: var(--negro); border-right: 1px solid var(--borde); }
[data-testid="stSidebar"] [data-testid="stElementContainer"],
[data-testid="stSidebar"] .stButton { width: 100% !important; }
[data-testid="stSidebar"] .stButton button { width: 100%; min-height: 3.6rem; justify-content: flex-start;
    text-align: left; border-radius: 8px; padding: 1rem 1.2rem; font-weight: 600;
    border: 1px solid var(--borde); background: #1B1B1B; }
[data-testid="stSidebar"] .stButton button * { color: #fff !important; font-size: 1.12rem; }
[data-testid="stSidebar"] .stButton button:hover { border-color: var(--verde); background: #242424; }
[data-testid="stSidebar"] .stButton button[kind="primary"],
[data-testid="stSidebar"] .stButton button[data-testid="stBaseButton-primary"] {
    background: var(--verde); border-color: var(--verde); }
[data-testid="stSidebar"] .stButton button[kind="primary"] *,
[data-testid="stSidebar"] .stButton button[data-testid="stBaseButton-primary"] * { color: #000 !important; }

/* Botones, formularios y métricas */
.stButton button, .stDownloadButton button, [data-testid="stFormSubmitButton"] button {
    width: 100%; border-radius: 4px; font-weight: 800; }
[data-testid="stMain"] .stButton button, [data-testid="stMain"] .stDownloadButton button,
[data-testid="stMain"] [data-testid="stFormSubmitButton"] button {
    background: #202020; border: 1px solid var(--borde); }
[data-testid="stMain"] .stButton button *, [data-testid="stMain"] .stDownloadButton button *,
[data-testid="stMain"] [data-testid="stFormSubmitButton"] button * { color: #fff !important; }
[data-testid="stMain"] .stButton button:hover, [data-testid="stMain"] .stDownloadButton button:hover,
[data-testid="stMain"] [data-testid="stFormSubmitButton"] button:hover { border-color: var(--verde); }
[data-testid="stMain"] .stButton button[kind="primary"],
[data-testid="stMain"] [data-testid="stFormSubmitButton"] button[kind="primary"],
[data-testid="stMain"] button[data-testid="stBaseButton-primary"],
[data-testid="stMain"] button[data-testid="stBaseButton-primaryFormSubmit"] {
    background: transparent; border: 2px solid var(--verde); text-transform: uppercase; letter-spacing: .5px; }
[data-testid="stMain"] button[kind="primary"] *, [data-testid="stMain"] button[data-testid="stBaseButton-primary"] *,
[data-testid="stMain"] button[data-testid="stBaseButton-primaryFormSubmit"] * { color: var(--verde) !important; }
[data-testid="stMain"] button[kind="primary"]:hover, [data-testid="stMain"] button[data-testid="stBaseButton-primary"]:hover,
[data-testid="stMain"] button[data-testid="stBaseButton-primaryFormSubmit"]:hover { background: var(--verde); }
[data-testid="stMain"] button[kind="primary"]:hover *, [data-testid="stMain"] button[data-testid="stBaseButton-primary"]:hover *,
[data-testid="stMain"] button[data-testid="stBaseButton-primaryFormSubmit"]:hover * { color: #000 !important; }
[data-testid="stForm"] { background: var(--panel); border: 1px solid var(--borde); border-radius: 12px;
    padding: 1.2rem 1.4rem; }
[data-testid="stMetric"] { background: var(--panel); border: 1px solid var(--borde); border-radius: 10px;
    padding: .6rem .9rem; }
[data-testid="stMetricValue"] { color: var(--verde); }
[data-testid="stMetricLabel"] * { color: var(--suave) !important; }

/* Componentes */
.titulo-pagina { display: flex; align-items: center; gap: .9rem; margin: .2rem 0 1rem; }
.titulo-pagina .ico { width: 54px; height: 54px; border-radius: 50%; background: var(--verde); color: #000;
    display: flex; align-items: center; justify-content: center; font-size: 1.6rem; flex: none; }
.titulo-pagina h2 { margin: 0; padding: 0; color: #fff !important; font-size: 1.9rem; }
.titulo-pagina p { margin: 0; color: var(--suave) !important; }
.panel-titulo { background: var(--negro); color: var(--verde); border: 1px solid var(--borde);
    border-bottom: 2px solid var(--verde); border-radius: 8px 8px 0 0; padding: .4rem .9rem;
    font-weight: 800; text-align: center; margin-top: .4rem; }
.tarjeta { background: var(--panel); border: 1px solid var(--borde); border-radius: 10px;
    padding: .8rem 1rem; height: 100%; }
.tarjeta .tt { font-size: .84rem; color: var(--suave); font-weight: 600; }
.tarjeta .tv { font-size: 1.4rem; font-weight: 800; color: #fff; line-height: 1.25; word-break: break-word; }
.tarjeta .sub { font-size: .8rem; color: var(--suave); }
.tarjeta.ok { background: #14210A; border-color: #4C7D0A; }
.tarjeta.ok .tv { color: var(--verde); }
.tarjeta.mal { background: #2A1315; border-color: #7A2E33; }
.tarjeta.mal .tv { color: #FF6B6B; }
.fichas { display: flex; flex-wrap: wrap; gap: 6px; margin-top: .4rem; }
.ficha { background: #2A2A2A; border: 1px solid var(--borde); border-radius: 6px; padding: .1rem .5rem;
    font-weight: 700; color: #fff; font-size: .82rem; }
.tarjeta.mal .ficha { background: #3A1A1D; border-color: #7A2E33; color: #FFB4B4; }
.bench { width: 100%; border-collapse: collapse; margin-top: .3rem; }
.bench td { padding: .25rem 0; border-bottom: 1px solid #333; color: #E6E6E6; font-size: .92rem; }
.bench td:last-child { text-align: right; font-weight: 800; color: var(--verde); }
.barras { display: flex; align-items: flex-end; gap: 6px; height: 130px; padding: .4rem .2rem 0; }
.barras .barra { flex: 1; background: #4A4A4A; border-radius: 4px 4px 0 0; }
.barras .barra.act { background: var(--verde); }
.pie-barras { text-align: center; font-size: .82rem; font-weight: 700; color: var(--suave); margin-top: .3rem; }
.ventana { display: flex; gap: 5px; }
.celda, .celda-f { flex: 1; min-width: 0; text-align: center; }
.celda { background: #2A2A2A; border: 1px solid var(--borde); border-radius: 6px; padding: .35rem .1rem;
    font-weight: 700; color: #fff; font-size: .76rem; white-space: nowrap; overflow: hidden;
    text-overflow: ellipsis; }
.celda.hit { background: var(--verde); border-color: var(--verde); color: #000; }
.celda-f { color: var(--verde); font-weight: 800; height: 1.2rem; }
.alfa-barra { position: relative; background: #2A2A2A; border: 1px solid var(--borde); border-radius: 6px;
    height: 36px; margin: .55rem 0; overflow: hidden; }
.alfa-barra .relleno { position: absolute; top: 0; bottom: 0; left: 0; background: #4A4A4A; }
.alfa-barra.alfa .relleno { background: var(--verde); }
.alfa-barra span { position: relative; color: #fff; font-weight: 700; padding: 0 .8rem; line-height: 34px; }
.alfa-barra.alfa span { color: #000; }
.creditos { margin-top: 1.6rem; background: var(--negro); color: #CFCFCF; border: 1px solid var(--borde);
    border-top: 2px solid var(--verde); border-radius: 10px; padding: .7rem 1rem; text-align: center;
    font-size: .9rem; display: flex; justify-content: center; gap: 1.2rem; flex-wrap: wrap; }
.creditos span { color: #CFCFCF !important; }
.acceso-icono { width: 74px; height: 74px; border-radius: 50%; background: var(--verde); color: #000;
    display: flex; align-items: center; justify-content: center; font-size: 2rem; margin: -2.6rem auto .6rem;
    border: 5px solid var(--panel); }
.acceso-titulo { text-align: center; font-size: 1.7rem; font-weight: 800; color: #fff; }
.acceso-sub { text-align: center; color: var(--suave); margin-bottom: .6rem; }
.intro-img { width: 100%; max-width: 280px; display: block; margin: 0 auto; }
</style>
"""

ESTILO_LOGIN = """
<style>
[data-testid="stSidebar"], [data-testid="stSidebarCollapsedControl"],
[data-testid="collapsedControl"] { display: none; }
</style>
"""


def cabecera(usuario=None):
    """Barra superior: título del proyecto y, con sesión iniciada, el menú del usuario."""
    col_marca, col_usuario = st.columns([5, 1.3])
    with col_marca:
        st.markdown(
            f'<div class="cabecera-marca"><img src="{SVG_ARBOL}" alt="">'
            f'<div class="sep"></div><div><div class="t1">Métodos de Ordenamiento y Búsqueda</div>'
            f'<div class="pill">⚓ {esc(TITULO_PROYECTO)}</div></div></div>',
            unsafe_allow_html=True)
    if usuario:
        with col_usuario:
            etiqueta = f"👤 {usuario} ▾"
            contenedor = st.popover(etiqueta) if hasattr(st, "popover") else st.expander(etiqueta)
            with contenedor:
                st.button("👤 Perfil", key="u_perfil", on_click=ir_a, args=("perfil",))
                st.button("⚙️ Configuración", key="u_config", on_click=ir_a, args=("config",))
                st.button("❓ Ayuda", key="u_ayuda", on_click=ir_a, args=("ayuda",))
                st.button("🚪 SALIR", key="u_salir", on_click=cerrar_sesion)


def creditos():
    st.markdown(
        f'<div class="creditos"><span>👨‍💻 {esc(CREDITOS_ALUMNOS)}</span><span>|</span>'
        f'<span>🤖 {esc(CREDITOS_IA)}</span></div>', unsafe_allow_html=True)


# =============================================================================
# 9. Pantallas
# =============================================================================
def pantalla_acceso():
    """Pantalla principal: registro / ingreso con clave opcional."""
    _, centro, _ = st.columns([1, 1.3, 1])
    with centro:
        with st.form("form_acceso"):
            st.markdown('<div class="acceso-icono">👥</div><div class="acceso-titulo">Registro de Usuario</div>'
                        '<div class="acceso-sub">Ingresa tus datos para comenzar a explorar los métodos '
                        'de ordenamiento y búsqueda.</div>', unsafe_allow_html=True)
            usuario = st.text_input("👤 Nombre de usuario", placeholder="Nombre de usuario")
            clave = st.text_input("🔒 Clave (opcional)", type="password", placeholder="Clave (opcional)")
            con_clave = st.form_submit_button("🔐 Registrarse / Ingresar", type="primary")
            sin_clave = st.form_submit_button("🚪 Ingresar sin clave")
        if con_clave or sin_clave:
            nombre, error = acceder(usuario, clave, sin_clave=sin_clave)
            if nombre:
                st.session_state.usuario = nombre
                st.session_state.pagina = "intro"
                st.rerun()
            st.error(error)
        st.caption("Si es tu primera vez, tu usuario se registra al ingresar. "
                   "La clave es opcional; si la pones, se te pedirá en tus próximas visitas.")


def pagina_intro():
    titulo_pagina("📘", "Introducción del Proyecto",
                  f"Bienvenido, {st.session_state.usuario}. Selecciona una opción del menú para "
                  "comenzar a explorar los métodos de ordenamiento y búsqueda.")
    izq, der = st.columns([1, 2])
    with izq:
        st.markdown(f'<img class="intro-img" src="{SVG_PORTADA}" alt="Ilustración del proyecto">',
                    unsafe_allow_html=True)
    with der:
        st.markdown("""
### 📌 ¿Qué es este proyecto?
Es una aplicación web para la **fiscalización y registro de tráfico en puertos marítimos**: carga
15,000 registros portuarios en la memoria RAM, los ordena con un algoritmo elegido al azar
(Radix, Bucket o Quick Sort), permite buscar un dato con búsqueda binaria o lineal y mide el
rendimiento de cada operación mediante un benchmarking.

### 🎯 ¿Qué se busca con él?
- 🧠 Comprender el funcionamiento de los algoritmos de ordenamiento y búsqueda.
- ⚖️ Comparar su rendimiento (tiempo, comparaciones y movimientos) en distintos escenarios.
- ⭐ Explorar el **Método Alfa**: qué algoritmo se selecciona más y cuál rinde mejor.

### 🔬 Investigación y profundidad
Se estudiaron los tres algoritmos de ordenamiento y las dos búsquedas, su complejidad, sus
ventajas y desventajas, y se aplicaron a un conjunto de datos de tráfico portuario. Las
referencias están en la opción **Fuentes**.
""")
    st.info("**En resumen:** este proyecto es una herramienta educativa y analítica para explorar, "
            "comparar y comprender los métodos de ordenamiento y búsqueda.")


def pagina_carga():
    titulo_pagina("🗄️", "Carga de Datos",
                  "Selecciona un archivo para cargar los datos y visualiza su información.")
    c1, c2, c3 = st.columns([1.3, 1.2, 1.2])
    with c1:
        archivo = st.file_uploader("📁 Seleccionar archivo (.csv o .txt)", type=["csv", "txt"],
                                   key="subida")
        if archivo is not None:
            firma = (archivo.name, archivo.size)
            if firma != st.session_state.get("firma_subida"):
                try:
                    cargar_fuente(archivo, archivo.name, archivo.size, "Archivo local")
                    st.session_state.firma_subida = firma
                except (KeyError, ValueError, UnicodeDecodeError) as error:
                    st.session_state.firma_subida = firma
                    st.error(f"No se pudo cargar el archivo: {error}")
    info = st.session_state.get("archivo")
    with c2:
        if info:
            st.markdown(tarjeta("✔ Archivo cargado:", info["nombre"],
                                f'<div class="sub">Tamaño: {formato_tamano(info["tamano"])}</div>',
                                "ok"), unsafe_allow_html=True)
        else:
            st.markdown(tarjeta("📄 Archivo cargado:", "Ninguno", clase="mal"), unsafe_allow_html=True)
    with c3:
        st.markdown(tarjeta("🗂️ Origen de los datos:", info["origen"] if info else "—"),
                    unsafe_allow_html=True)

    if "registros_base" not in st.session_state:
        st.warning(f"No se encontró `{NOMBRE_CSV}` junto a la aplicación. Selecciona un archivo "
                   "para continuar.")
        return

    registros = st.session_state.registros_base
    n_total = len(registros)
    col_ok, col_t = st.columns([2, 1])
    col_ok.success(f"[ÉXITO] Se cargaron {n_total:,} registros a la memoria RAM "
                   f"({len(TODOS_LOS_CAMPOS)} columnas por registro).")
    col_t.metric("⏱ Tiempo de carga a la RAM", f"{st.session_state.tiempo_carga:,} ns")
    if n_total != TOTAL_ESPERADO:
        st.warning(f"Se esperaban {TOTAL_ESPERADO:,} registros y el archivo tiene {n_total:,}.")

    muestra = registros[0]
    st.dataframe(
        pd.DataFrame({
            "CAMPO": [NOMBRES_CAMPOS[c] for c in TODOS_LOS_CAMPOS],
            "ROL": ["Clave" if c in CAMPOS_CLAVE else "Informativo" for c in TODOS_LOS_CAMPOS],
            "TIPO EN MEMORIA": [type(getattr(muestra, c)).__name__ for c in TODOS_LOS_CAMPOS],
            "ORIGEN": ["Archivo"] * len(TODOS_LOS_CAMPOS),
            "DESCRIPCIÓN": [DESCRIPCIONES[c] for c in TODOS_LOS_CAMPOS],
        }),
        hide_index=True,
    )
    n = cantidad_selector("cant_carga")
    tablas_primeros_ultimos(registros, n)


def pagina_orden():
    titulo_pagina("↕️", "Ordenación",
                  "Ejecuta el ordenamiento sobre los datos no ordenados y observa el proceso.")
    if not requiere_datos():
        return
    res = st.session_state.get("resultado")

    c1, c2, c3 = st.columns([1, 1.3, 1.1])
    with c1:
        st.button("▶ Ejecutar ordenación", type="primary", on_click=ejecutar_ronda,
                  key="btn_ordenar")
    with c2:
        st.markdown(tarjeta("🎲 Método seleccionado aleatoriamente:",
                            res["metodo"] if res else "Pulsa «Ejecutar ordenación»"),
                    unsafe_allow_html=True)
    with c3:
        n = cantidad_selector("cant_orden")

    campo = res["campo"] if res else CAMPOS_CLAVE[0]
    originales = [valor_texto(r, campo) for r in st.session_state.registros_base[:10]]
    a, b, c = st.columns([1, 1.5, 1])
    with a:
        st.markdown(tarjeta("⚠ Datos originales:", "NO ORDENADOS", html_fichas(originales), "mal"),
                    unsafe_allow_html=True)
    with b:
        with st.container(border=True):
            st.markdown("**📊 Proceso de Ordenamiento**")
            zona = st.empty()
            if res is None:
                zona.info("Pulsa «Ejecutar ordenación» para ver el proceso.")
            else:
                cuadros = trazas_ordenamiento(res["metodo"], res["muestra"])
                if st.session_state.pop("animar", False):
                    reproducir_animacion(zona, cuadros)
                else:
                    zona.markdown(html_barras(cuadros[-1][0])
                                  + '<div class="pie-barras">✔ Ordenado</div>',
                                  unsafe_allow_html=True)
                st.caption(f"Vista didáctica con una muestra de {len(res['muestra'])} datos de "
                           f"{NOMBRES_CAMPOS[res['campo']]}.")
    with c:
        if res:
            filas = [("⏱ Tiempo de ejecución:", f"{res['ns_orden']:,} ns"),
                     ("🕐 Equivale a:", f"{res['ns_orden'] / 1e9:.6f} s"),
                     ("🔁 Comparaciones:", f"{res['comparaciones']:,}"),
                     ("🔀 Intercambios:", f"{res['movimientos']:,}")]
        else:
            filas = [("⏱ Tiempo de ejecución:", "—"), ("🕐 Equivale a:", "—"),
                     ("🔁 Comparaciones:", "—"), ("🔀 Intercambios:", "—")]
        tabla = "".join(f"<tr><td>{k}</td><td>{v}</td></tr>" for k, v in filas)
        st.markdown(f'<div class="tarjeta"><div class="tt">⏱ Benchmarking</div>'
                    f'<table class="bench">{tabla}</table></div>', unsafe_allow_html=True)

    if res is None:
        st.info("Aquí aparecerán los registros ordenados.")
        return
    st.info(f"Se ordenaron {len(res['registros_ordenados']):,} registros por el campo "
            f"{res['campo']} usando el método {res['metodo']} en {res['ns_orden']} nanosegundos. "
            f"Comparaciones: {res['comparaciones']}, Intercambios/Movimientos: {res['movimientos']}")
    tablas_primeros_ultimos(res["registros_ordenados"], n, "🔢 Registros ordenados — primeros",
                            "🔢 Registros ordenados — últimos")
    st.download_button("⬇️ Descargar lista ordenada (.txt)", data=res["txt"],
                       file_name=f"registros_ordenados_por_{res['campo']}.txt",
                       mime="text/plain")


def pagina_busqueda():
    titulo_pagina("🔍", "Búsqueda", "Ejecuta una búsqueda aleatoria y observa el resultado.")
    if not requiere_datos():
        return
    res = st.session_state.get("resultado")
    tipo = st.session_state.get("busq_tipo")
    if tipo == "Binaria" and res is None:
        tipo = None

    c1, c2, c3 = st.columns([1, 1.2, 1.7])
    with c1:
        st.button("▶ Ejecutar búsqueda", type="primary", on_click=disparador_busqueda,
                  key="btn_disparo_busqueda")
    with c2:
        st.markdown(tarjeta("🎲 Método seleccionado aleatoriamente:",
                            f"Búsqueda {tipo}" if tipo else "Pulsa «Ejecutar búsqueda»"),
                    unsafe_allow_html=True)
    with c3:
        with st.container(border=True):
            if tipo is None:
                st.caption("Después de ejecutar la búsqueda podrás elegir el registro a buscar.")
            else:
                if tipo == "Binaria":
                    campo_busq = res["campo"]
                    st.markdown(f"**Registro a buscar** · campo **{NOMBRES_CAMPOS[campo_busq]}** "
                                f"(ordenado con {res['metodo']})")
                else:
                    campo_busq = st.selectbox(
                        "Registro a buscar · elegir campo (1-10)", TODOS_LOS_CAMPOS,
                        key="busq_campo", on_change=cambio_campo_busqueda,
                        format_func=lambda c: f"Campo {TODOS_LOS_CAMPOS.index(c) + 1}: "
                                              f"{NOMBRES_CAMPOS[c]}")
                lista_actual = res["registros_ordenados"] if res else st.session_state.registros_base
                with st.form("form_busqueda"):
                    ejemplo = valor_texto(lista_actual[0], campo_busq)
                    st.text_input(f"Dato a buscar en {NOMBRES_CAMPOS[campo_busq]}", key="busq_valor",
                                  placeholder=f"Ejemplo: {ejemplo}")
                    st.form_submit_button("🔍 Buscar", type="primary", on_click=lanzar_busqueda)
                st.caption("Campos numéricos: escribe el número. Campos de texto: coincidencia "
                           "exacta (mayúsculas y minúsculas). Si hay varios registros con el mismo "
                           "valor (peso, fecha, etc.) se muestran todos.")

    b = st.session_state.get("ultima_busqueda")
    if b is None:
        st.info("Aquí aparecerá el resultado de la búsqueda.")
        return
    if "error" in b:
        st.error(b["error"])
        return

    posiciones = b["posiciones"]
    encontrado = bool(posiciones)
    a1, a2, a3 = st.columns([1.1, 1.6, 1])
    with a1:
        if encontrado:
            reg = b["registros"][0]
            detalle = (f'<div class="sub">ID: {reg.id_contenedor_teu} | Peso: {reg.peso_bruto_kg:,} kg<br>'
                       f'Fecha: {reg.fecha_atracadero} | {esc(reg.puerto_operacion)}</div>'
                       f'<div class="sub"><b>Posición: {posiciones[0] + 1:,}</b>'
                       + (f" (+{len(posiciones) - 1:,} coincidencias más)" if len(posiciones) > 1 else "")
                       + "</div>")
            st.markdown(tarjeta("✔ Registro encontrado", f"{len(posiciones):,} coincidencia(s)",
                                detalle, "ok"), unsafe_allow_html=True)
        else:
            st.markdown(tarjeta("✖ No encontrado", "0 coincidencias",
                                '<div class="sub">No existe ningún registro con ese valor en ese campo.</div>',
                                "mal"), unsafe_allow_html=True)
    with a2:
        with st.container(border=True):
            st.markdown("**🧭 Proceso de Búsqueda**")
            if encontrado:
                st.markdown(html_ventana(b["ventana"]), unsafe_allow_html=True)
                st.caption(f"Valores de {NOMBRES_CAMPOS[b['campo']]} alrededor de la primera "
                           "coincidencia (en verde). Pasa el cursor sobre una celda para ver su posición.")
            else:
                st.caption("Búsqueda completada sin coincidencias.")
    with a3:
        filas = [("🔎 Tipo:", b["tipo"]), ("⏱ Tiempo de ejecución:", f"{b['ns']:,} ns"),
                 ("🔁 Comparaciones / pasos:", f"{b['pasos']:,}"),
                 ("🎯 Coincidencias:", f"{len(posiciones):,}")]
        tabla = "".join(f"<tr><td>{k}</td><td>{esc(v)}</td></tr>" for k, v in filas)
        st.markdown(f'<div class="tarjeta"><div class="tt">⏱ Benchmarking</div>'
                    f'<table class="bench">{tabla}</table></div>', unsafe_allow_html=True)
    st.caption(f"Búsqueda {b['tipo']} sobre {b['campo']} del valor {b['objetivo']!r}. La posición "
               "se cuenta dentro de la lista "
               + (f"ordenada por {b['orden']}." if b["orden"] else "en su orden original (sin ordenar)."))
    if encontrado:
        panel_titulo(f"✅ Registros encontrados ({len(posiciones):,})")
        df = pd.DataFrame([vars(r) for r in b["registros"]])
        df.insert(0, "posicion", [p + 1 for p in posiciones])
        st.dataframe(df, hide_index=True,
                     column_config={"posicion": st.column_config.NumberColumn("Posición", format="%d"),
                                    **COLUMNAS})


def pagina_reportes():
    titulo_pagina("📊", "Reportes",
                  "Consulta el benchmarking de ordenación, el de búsqueda o el análisis comparativo.")
    tab_o, tab_b, tab_c = st.tabs(["⏱ Benchmarking de Ordenación", "🔎 Benchmarking de Búsqueda",
                                   "⚖️ Análisis Comparativo"])
    historial = obtener_bitacora()["datos"]["historial"]
    res = st.session_state.get("resultado")

    with tab_o:
        filas = [f for f in historial if f["Evento"] == "Ordenación"][::-1]
        if not filas:
            st.info("Aún no hay ordenaciones. Ejecuta la ordenación para ver su benchmarking.")
        else:
            ultima = filas[0]
            m1, m2, m3, m4 = st.columns(4)
            m1.metric("🧮 Método", ultima["Método / tipo"])
            m2.metric("🏷️ Campo ordenado", ultima["Campo"])
            m3.metric("⏱ Tiempo (ns)", f"{ultima['Tiempo (ns)']:,}")
            m4.metric("🔁 Comparaciones / Movimientos",
                      f"{ultima['Comparaciones']:,} / {ultima['Movimientos']:,}")
            panel_titulo("🕒 Historial de ordenaciones (más recientes primero)")
            df = pd.DataFrame(filas)[["Hora", "Método / tipo", "Campo", "Tiempo (ns)",
                                      "Comparaciones", "Movimientos"]]
            st.dataframe(df, hide_index=True, column_config={
                c: st.column_config.NumberColumn(c, format="%d")
                for c in ["Tiempo (ns)", "Comparaciones", "Movimientos"]})
            if res:
                st.download_button("⬇️ Descargar lista ordenada (.txt)", data=res["txt"],
                                   file_name=f"registros_ordenados_por_{res['campo']}.txt",
                                   mime="text/plain", key="dl_txt_reportes")

    with tab_b:
        filas = [f for f in historial if f["Evento"] == "Búsqueda"][::-1]
        if not filas:
            st.info("Aún no hay búsquedas. Ejecuta una búsqueda para ver su benchmarking.")
        else:
            panel_titulo("🕒 Historial de búsquedas (más recientes primero)")
            df = pd.DataFrame(filas)[["Hora", "Método / tipo", "Campo", "Valor buscado",
                                      "Resultado", "Tiempo (ns)", "Pasos"]]
            st.dataframe(df, hide_index=True, column_config={
                c: st.column_config.NumberColumn(c, format="%d") for c in ["Tiempo (ns)", "Pasos"]})

    with tab_c:
        st.markdown("**⚖️ Análisis Comparativo por los 3 Campos Clave**")
        if "registros_base" not in st.session_state:
            st.warning("Primero carga los datos en la opción **Carga de Datos** del menú.")
        else:
            st.button("⏱ Medir los 3 campos clave ahora", on_click=medir_comparativo,
                      key="btn_comparativo")
            st.caption("Ordena una copia de los datos por cada campo clave con su algoritmo. "
                       "Esta medición no modifica el Método Alfa.")
            comparativo = st.session_state.get("comparativo")
            if comparativo is None:
                st.info("Pulsa el botón para generar la comparación.")
            else:
                st.dataframe(pd.DataFrame({
                    "CAMPO CLAVE": [NOMBRES_CAMPOS[f["campo"]] for f in comparativo],
                    "TIPO DE DATO": ["Numérico (entero)"] * len(comparativo),
                    "MÉTODO DE ORDENAMIENTO": [f["metodo"] for f in comparativo],
                    "TIEMPO (ns)": [f["ns"] for f in comparativo],
                    "TIEMPO (s)": [round(f["ns"] / 1e9, 6) for f in comparativo],
                    "COMPARACIONES": [f["comparaciones"] for f in comparativo],
                    "MOVIMIENTOS": [f["movimientos"] for f in comparativo],
                }), hide_index=True)
                panel_titulo("📈 Comparación gráfica por campo clave y método")
                grafica_comparativa(comparativo)
                st.caption("Cada campo clave se ordena con un algoritmo distinto, por lo que la "
                           "comparación mezcla el efecto del campo y el del método.")

    historial_csv = pd.DataFrame(historial[::-1]) if historial else None
    if historial_csv is not None:
        st.download_button("⬇️ Descargar bitácora de la sesión (.csv)",
                           data=historial_csv.to_csv(index=False).encode("utf-8-sig"),
                           file_name="bitacora_alfa.csv", mime="text/csv", key="dl_csv_bitacora")


def pagina_alfa():
    titulo_pagina("⭐", "Método Alfa",
                  "Visualiza el algoritmo Alfa del usuario registrado y el Alfa general mediante "
                  "gráficas de barras.")
    usuario_d = obtener_bitacora()["datos"]
    general_d = obtener_general()["datos"]
    fu, ru = calcular_alfa(usuario_d["metodos"])
    fg, rg = calcular_alfa(general_d["metodos"])

    c1, c2, c3 = st.columns(3)
    with c1:
        st.markdown(tarjeta("★ Alfa Usuario:", " / ".join(fu) if fu else "Sin rondas aún"),
                    unsafe_allow_html=True)
    with c2:
        st.markdown(tarjeta("🏆 Alfa General:", " / ".join(fg) if fg else "Sin rondas aún"),
                    unsafe_allow_html=True)
    with c3:
        st.button("🔄 Reiniciar Alfa del Usuario", on_click=reiniciar_alfa_usuario, key="btn_reiniciar_alfa")
        st.caption("No afecta el Alfa General.")

    g1, g2 = st.columns(2)
    with g1:
        panel_titulo("👤 Método Alfa — Usuario registrado")
        st.markdown(html_alfa(usuario_d["metodos"], fu), unsafe_allow_html=True)
    with g2:
        panel_titulo("🌐 Método Alfa — General")
        st.markdown(html_alfa(general_d["metodos"], fg), unsafe_allow_html=True)
    st.caption("El porcentaje es la proporción de rondas en que se seleccionó cada método. "
               "El Alfa del usuario empieza en 0 cada vez que entras.")

    def fila(ambito, datos, alfa_f, alfa_r, estado):
        pct = porcentajes(datos["metodos"])
        return {
            "ÁMBITO": ambito,
            "ALGORITMO ALFA (FRECUENCIA)": (" / ".join(alfa_f) + " ★") if alfa_f else "—",
            "ALFA POR RENDIMIENTO": " / ".join(alfa_r) if alfa_r else "—",
            "PUNTAJE": f"{max(pct.values())}%" if alfa_f else "—",
            "RONDAS": datos["rondas"],
            "ESTADO DE CONTROL": estado,
        }
    panel_titulo("📋 Detalle comparativo del Método Alfa")
    st.dataframe(pd.DataFrame([
        fila("Usuario registrado", usuario_d, fu, ru, "Reiniciable de forma independiente"),
        fila("General (acumulado global)", general_d, fg, rg, "Protegido (sin afectación por reinicio)"),
    ]), hide_index=True)

    filas = []
    for metodo in METODOS:
        s = usuario_d["metodos"][metodo]
        v = s["veces"]
        filas.append({
            "Método": metodo, "Veces seleccionado": v,
            "Tiempo promedio (ns)": round(s["ns_total"] / v) if v else None,
            "Comparaciones promedio": round(s["comparaciones_total"] / v) if v else None,
            "Movimientos promedio": round(s["movimientos_total"] / v) if v else None,
        })
    panel_titulo("📊 Promedios del usuario por método")
    st.dataframe(pd.DataFrame(filas), hide_index=True)


def pagina_fuentes():
    titulo_pagina("📖", "Fuentes",
                  "Referencias bibliográficas en formato APA y recursos utilizados en la elaboración "
                  "del proyecto.")
    panel_titulo("📚 Referencias bibliográficas (formato APA)")
    st.markdown("""
- 📖 Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2022). *Introduction to algorithms* (4th ed.). MIT Press.
- 📖 Knuth, D. E. (1998). *The art of computer programming: Vol. 3. Sorting and searching* (2nd ed.). Addison-Wesley.
- 📖 Sedgewick, R., & Wayne, K. (2011). *Algorithms* (4th ed.). Addison-Wesley Professional.
""")
    panel_titulo("🛠️ Recursos y herramientas utilizadas")
    st.dataframe(pd.DataFrame({
        "CATEGORÍA": ["Diseño UI / UX", "Desarrollo", "Desarrollo", "Inteligencia Artificial",
                      "Fuente de datos"],
        "RECURSO / HERRAMIENTA": ["Maqueta de interfaz (Avance 2)", "Python 3 y Streamlit",
                                  "pandas y Altair", "Claude (Anthropic)", f"Archivo {NOMBRE_CSV}"],
        "APLICACIÓN EN EL PROYECTO": [
            "Maquetación centrada en el usuario",
            "Implementación de algoritmos y vistas",
            "Tablas y gráficas de resultados",
            "Apoyo en el diseño visual, la estructura y el desarrollo de la interfaz web",
            "Conjunto de prueba y benchmarking (puertos y fechas reales de SEMAR; pesos, costos, "
            "navieras y estatus simulados)"],
    }), hide_index=True)


def pagina_perfil():
    usuario = st.session_state.usuario
    titulo_pagina("👤", "Perfil", "Tus datos de cuenta y el registro de las personas que entraron.")
    mio = next((r for r in resumen_por_persona() if r["Usuario"].lower() == usuario.lower()), None)
    c1, c2, c3, c4 = st.columns(4)
    c1.markdown(tarjeta("👤 Usuario", usuario), unsafe_allow_html=True)
    c2.markdown(tarjeta("🔑 Clave", "Con clave" if cuenta_tiene_clave(usuario) else "Sin clave"),
                unsafe_allow_html=True)
    c3.markdown(tarjeta("🔢 Veces que entraste", f"{mio['Veces que entró']:,}" if mio else "—"),
                unsafe_allow_html=True)
    c4.markdown(tarjeta("📅 Cuenta creada", mio["Cuenta creada"] if mio and mio["Cuenta creada"] else "—"),
                unsafe_allow_html=True)

    st.markdown("### 👥 Registro de personas que entraron")
    resumen = resumen_por_persona()
    historial_acc = list(_accesos())
    a1, a2, a3 = st.columns(3)
    a1.metric("👥 Cuentas registradas", len(resumen))
    a2.metric("🚶 Personas que han entrado", sum(1 for r in resumen if r["Veces que entró"] > 0))
    a3.metric("🔑 Inicios de sesión", sum(1 for f in historial_acc if f["Evento"] == "Inicio de sesión"))

    panel_titulo("👥 Por persona")
    if resumen:
        st.dataframe(pd.DataFrame(resumen), hide_index=True,
                     column_config={"Veces que entró": st.column_config.NumberColumn(format="%d")})
    else:
        st.info("Aún no hay cuentas registradas.")

    panel_titulo("🕒 Historial de accesos (más recientes primero)")
    if historial_acc:
        df_acc = pd.DataFrame(historial_acc[::-1])
        st.dataframe(df_acc, hide_index=True)
        st.download_button("⬇️ Descargar registro de accesos (.csv)",
                           data=df_acc.to_csv(index=False).encode("utf-8-sig"),
                           file_name="registro_accesos.csv", mime="text/csv")
    else:
        st.info("Todavía no hay accesos registrados.")
    st.caption("Se registran inicios de sesión, cuentas creadas, cierres de sesión e intentos "
               f"fallidos. Se guarda en `{ARCHIVO_ACCESOS.name}`.")


def pagina_config():
    usuario = st.session_state.usuario
    titulo_pagina("⚙️", "Configuración", "Ajusta la vista de la aplicación y la clave de tu cuenta.")
    st.markdown("### 🖥️ Vista")
    actual = st.session_state.get("cant_registros", 30)
    st.session_state.cant_registros = st.selectbox(
        "Cantidad de registros a visualizar por defecto", OPCIONES_CANTIDAD,
        index=OPCIONES_CANTIDAD.index(actual) if actual in OPCIONES_CANTIDAD else 2,
        key="cant_config")

    st.markdown("### 🔑 Clave de la cuenta")
    tiene = cuenta_tiene_clave(usuario)
    st.caption("Tu cuenta tiene clave." if tiene else "Tu cuenta no tiene clave: cualquiera puede "
               "entrar con tu nombre. Puedes agregar una.")
    with st.form("form_clave"):
        actual_clave = st.text_input("Clave actual", type="password") if tiene else ""
        nueva = st.text_input("Clave nueva (déjala vacía para quitar la clave)"
                              if tiene else "Clave nueva", type="password")
        guardar = st.form_submit_button("Guardar clave", type="primary")
    if guardar:
        ok, mensaje = cambiar_clave(usuario, actual_clave, nueva)
        (st.success if ok else st.error)(mensaje)


def pagina_ayuda():
    titulo_pagina("❓", "Ayuda", "Cómo usar la aplicación paso a paso.")
    st.markdown(f"""
1. 🗄️ **Carga de Datos:** al entrar se cargan automáticamente los registros de `{NOMBRE_CSV}`
   (si está junto a la aplicación). También puedes seleccionar otro archivo `.csv` o `.txt`.
2. ↕️ **Ordenación:** pulsa *Ejecutar ordenación*. El disparador elige al azar el algoritmo
   (Radix, Bucket o Quick Sort), muestra el proceso y mide tiempo, comparaciones e intercambios.
3. 🔍 **Búsqueda:** pulsa *Ejecutar búsqueda*. El disparador elige al azar búsqueda lineal o binaria.
   En la lineal eliges cualquiera de los 10 campos; la binaria usa el campo recién ordenado
   (necesita haber ordenado antes). Escribe el dato y pulsa *Buscar*: se muestran todas las coincidencias.
4. 📊 **Reportes:** historial de benchmarking de ordenación y de búsqueda, y el análisis comparativo
   de los 3 campos clave.
5. ⭐ **Método Alfa:** el del usuario empieza en 0 cada vez que entras y puede reiniciarse; el general
   acumula a todas las personas y no se reinicia.
6. 📖 **Fuentes:** referencias en formato APA y recursos utilizados.
""")


PAGINAS = {
    "intro": pagina_intro, "carga": pagina_carga, "orden": pagina_orden,
    "busqueda": pagina_busqueda, "reportes": pagina_reportes, "alfa": pagina_alfa,
    "fuentes": pagina_fuentes, "perfil": pagina_perfil, "config": pagina_config,
    "ayuda": pagina_ayuda,
}


# =============================================================================
# 10. Aplicación web
# =============================================================================
st.set_page_config(page_title="Proyecto 21 - Puertos Marítimos", page_icon="⚓",
                   layout="wide", initial_sidebar_state="expanded")
st.markdown(ESTILO, unsafe_allow_html=True)

# Estado persistente de la sesión (sobrevive a las recargas de Streamlit)
st.session_state.setdefault("pagina", "intro")
st.session_state.setdefault("cant_registros", 30)
st.session_state.setdefault("ultima_busqueda", None)

# --- Pantalla principal: registro / ingreso ---
if "usuario" not in st.session_state:
    st.markdown(ESTILO_LOGIN, unsafe_allow_html=True)
    cabecera()
    pantalla_acceso()
    creditos()
    st.stop()

cabecera(st.session_state.usuario)

# --- Carga automática del CSV del proyecto (una sola vez por sesión) ---
if "registros_base" not in st.session_state:
    ruta = Path(__file__).resolve().parent / NOMBRE_CSV
    if not ruta.exists():
        ruta = Path.cwd() / NOMBRE_CSV
    if ruta.exists():
        try:
            cargar_fuente(ruta, ruta.name, ruta.stat().st_size, "CSV del proyecto")
        except (KeyError, ValueError, UnicodeDecodeError, OSError) as error:
            st.error(f"No se pudo cargar {NOMBRE_CSV}: {error}")

# --- Menú lateral fijo ---
with st.sidebar:
    for clave, icono, texto in MENU:
        st.button(f"{icono}  {texto}", key=f"menu_{clave}",
                  type="primary" if st.session_state.pagina == clave else "secondary",
                  on_click=ir_a, args=(clave,))

# --- Área central ---
PAGINAS.get(st.session_state.pagina, pagina_intro)()
creditos()
