"""
PROYECTO 21: FISCALIZACIÓN Y REGISTRO DE TRÁFICO EN PUERTOS MARÍTIMOS
Aplicación web (Streamlit)

Ejecutar:
    pip install streamlit
    streamlit run app.py

Coloca dataset_puertos_15000.csv en la misma carpeta que este archivo
(si no está, la app te permite subirlo desde el navegador).
"""
import csv
import io
import math
import random
import time
from pathlib import Path

import altair as alt
import pandas as pd
import streamlit as st

NOMBRE_CSV = "dataset_puertos_15000.csv"


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
        archivo_csv = io.StringIO(fuente.getvalue().decode("utf-8"))
    else:
        archivo_csv = open(fuente, mode="r", encoding="utf-8", newline="")

    with archivo_csv:
        lector = csv.DictReader(archivo_csv)
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
    """Requiere la lista ordenada por `campo`. Retorna (posicion, ns, pasos)."""
    inicio = time.perf_counter_ns()
    lo, hi = 0, len(registros) - 1
    posicion, pasos = -1, 0
    while lo <= hi:
        pasos += 1
        medio = (lo + hi) // 2
        valor = getattr(registros[medio], campo)
        if valor == objetivo:
            posicion = medio
            break
        if valor < objetivo:
            lo = medio + 1
        else:
            hi = medio - 1
    return posicion, time.perf_counter_ns() - inicio, pasos


def busqueda_lineal(registros, campo, objetivo):
    """Recorrido secuencial sobre cualquier campo. Retorna (posicion, ns, pasos)."""
    inicio = time.perf_counter_ns()
    posicion, pasos = -1, 0
    for i, reg in enumerate(registros):
        pasos += 1
        if getattr(reg, campo) == objetivo:
            posicion = i
            break
    return posicion, time.perf_counter_ns() - inicio, pasos


# =============================================================================
# 5. Ronda completa: ordenar -> buscar -> actualizar Método Alfa
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


def ejecutar_ronda():
    # Cada ronda parte del orden original del CSV
    registros_ram = list(st.session_state.registros_base)

    # Disparador aleatorio de ordenación (el campo determina el método)
    opcion = random.randint(1, 3)
    campo, metodo, funcion_orden = MOTOR_ORDENACION[opcion]
    tiempo_ns, comparaciones, movimientos = funcion_orden(registros_ram)

    # Verificación de correctitud (fuera de la medición)
    if not esta_ordenado(registros_ram, campo):
        raise RuntimeError(f"La lista no quedó ordenada por {campo}")

    # Método Alfa: contador de veces que se seleccionó cada método
    st.session_state.alfa[metodo] += 1
    st.session_state.rondas += 1

    # Disparador aleatorio de búsqueda (50/50)
    tipo_busqueda = random.choice(["Binaria", "Lineal"])
    if tipo_busqueda == "Binaria":
        campo_busq = campo                                   # el campo ya ordenado
        objetivo = getattr(random.choice(registros_ram), campo_busq)
        posicion, ns_busq, pasos = busqueda_binaria(registros_ram, campo_busq, objetivo)
    else:
        campo_busq = random.choice(TODOS_LOS_CAMPOS)         # clave o informativo
        objetivo = getattr(random.choice(registros_ram), campo_busq)
        posicion, ns_busq, pasos = busqueda_lineal(registros_ram, campo_busq, objetivo)

    st.session_state.resultado = {
        "registros_ordenados": registros_ram,
        "campo": campo, "metodo": metodo,
        "ns_orden": tiempo_ns, "comparaciones": comparaciones, "movimientos": movimientos,
        "tipo_busqueda": tipo_busqueda, "campo_busqueda": campo_busq,
        "objetivo": objetivo, "posicion": posicion, "ns_busqueda": ns_busq, "pasos": pasos,
        "txt": generar_txt_ordenado(registros_ram, campo, metodo, tiempo_ns,
                                    comparaciones, movimientos),
    }


# =============================================================================
# 6. Utilidades de interfaz
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


def mostrar_30_30(registros):
    n = len(registros)
    st.markdown("**Primeros 30 registros**")
    st.dataframe(a_dataframe(registros[:30], 1), column_config=COLUMNAS)
    st.caption(f"... {n - 60:,} registros intermedios ocultos para no saturar la vista ...")
    st.markdown("**Últimos 30 registros**")
    st.dataframe(a_dataframe(registros[-30:], n - 29), column_config=COLUMNAS)


# =============================================================================
# 7. Aplicación web
# =============================================================================
st.set_page_config(page_title="Proyecto 21 - Puertos Marítimos", page_icon="⚓",
                   layout="wide", initial_sidebar_state="expanded")

# Estilo visual. Colores de acento: #00B4D8 (mismo primario de .streamlit/config.toml).
st.markdown("""
<style>
.hero { background: linear-gradient(135deg, #0A1931 0%, #13294B 55%, #0b6f8a 130%);
        padding: 1.6rem 1.8rem; border-radius: 16px;
        border: 1px solid rgba(255,255,255,0.12); margin-bottom: 1rem; }
.hero h1 { margin: 0.4rem 0 0.4rem 0; padding: 0; font-size: 1.9rem; line-height: 1.2;
           color: #F1F5F9; letter-spacing: 0.5px; }
.hero p { margin: 0; color: #CBD5E1; font-size: 1.02rem; }
.hero-badge { display: inline-block; background: rgba(0,180,216,0.22); color: #7DD3F5;
              padding: 0.15rem 0.75rem; border-radius: 999px; font-size: 0.8rem;
              font-weight: 600; letter-spacing: 1px; }
.paso { border-radius: 12px; padding: 0.8rem 1rem; height: 100%;
        border: 1px solid rgba(255,255,255,0.14); background: rgba(255,255,255,0.04); }
.paso.hecho { border-color: #00B4D8; background: rgba(0,180,216,0.12); }
.paso .n { display: inline-block; min-width: 1.5rem; font-weight: 700; color: #00B4D8; }
.paso .t { font-weight: 600; }
.paso .d { font-size: 0.85rem; opacity: 0.75; margin-top: 0.2rem; }
[data-testid="stMetric"] { background: rgba(255,255,255,0.04);
        border: 1px solid rgba(255,255,255,0.10); border-radius: 12px; padding: 0.7rem 1rem; }
[data-testid="stMetricValue"] { font-size: 1.7rem; color: #00B4D8; }
[data-testid="stMetricValue"] div {
    white-space: normal; overflow: visible; text-overflow: clip; overflow-wrap: anywhere; }
[data-testid="stMetricLabel"] { opacity: 0.8; }
#MainMenu, footer { visibility: hidden; }
</style>
""", unsafe_allow_html=True)


# Un color distinto por método de ordenamiento
COLORES_METODOS = {
    "Radix Sort": "#00B4D8",    # cian
    "Bucket Sort": "#F5A524",   # ámbar
    "Quick Sort": "#A78BFA",    # violeta
}


def grafica_alfa(conteos):
    """Barras horizontales con un color por método (Método Alfa)."""
    df = pd.DataFrame({"Metodo": list(conteos.keys()), "Veces": list(conteos.values())})
    barras = (
        alt.Chart(df)
        .mark_bar(cornerRadiusTopRight=4, cornerRadiusBottomRight=4)
        .encode(
            y=alt.Y("Metodo:N", sort=None, title=None),
            x=alt.X("Veces:Q", title="Veces seleccionado",
                    axis=alt.Axis(tickMinStep=1, format="d")),
            color=alt.Color(
                "Metodo:N",
                scale=alt.Scale(domain=list(COLORES_METODOS.keys()),
                                range=list(COLORES_METODOS.values())),
                legend=None,
            ),
            tooltip=[alt.Tooltip("Metodo:N", title="Método"),
                     alt.Tooltip("Veces:Q", title="Veces seleccionado")],
        )
        .properties(height=150)
    )
    st.altair_chart(barras)


def tarjeta_paso(numero, titulo, detalle, hecho):
    clase = "paso hecho" if hecho else "paso"
    marca = "✓" if hecho else numero
    return (f'<div class="{clase}"><span class="n">{marca}</span> '
            f'<span class="t">{titulo}</span><div class="d">{detalle}</div></div>')


# Estado persistente (sobrevive a las recargas de Streamlit)
if "alfa" not in st.session_state:
    st.session_state.alfa = {m: 0 for m in METODOS}
    st.session_state.rondas = 0

# --- Encabezado ---
st.markdown("""
<div class="hero">
<span class="hero-badge">⚓ PROYECTO 21</span>
<h1>Fiscalización y Registro de Tráfico en Puertos Marítimos</h1>
<p>Ordena y busca entre 15,000 registros portuarios y compara el rendimiento de los algoritmos.</p>
</div>
""", unsafe_allow_html=True)
st.write(
    "Aplicación que carga 15,000 registros portuarios (puertos y fechas reales de los datos de "
    "SEMAR, con campos numéricos simulados) en la memoria RAM como objetos `RegistroPortuario`, "
    "los ordena con un algoritmo elegido al azar (Radix, Bucket o Quick Sort), busca un dato con "
    "Búsqueda Binaria o Lineal y mide tiempos, comparaciones y movimientos."
)

# --- Carga a RAM (una sola vez por sesión) ---
if "registros_base" not in st.session_state:
    ruta = Path(__file__).resolve().parent / NOMBRE_CSV
    if not ruta.exists():
        ruta = Path.cwd() / NOMBRE_CSV
    fuente = ruta if ruta.exists() else None
    if fuente is None:
        st.warning(f"No se encontró `{NOMBRE_CSV}` junto a la aplicación. Súbelo para continuar.")
        fuente = st.file_uploader("Selecciona el CSV", type="csv")
        if fuente is None:
            st.stop()
    registros, tiempo_carga = cargar_datos_en_ram(fuente)
    st.session_state.registros_base = registros
    st.session_state.tiempo_carga = tiempo_carga

# NO se ordena al entrar: los datos aparecen tal como vienen en el CSV (sin ordenar)
# y solo el botón "Ejecutar disparador" lanza la ordenación y la búsqueda.
n_total = len(st.session_state.registros_base)
res = st.session_state.get("resultado")          # None hasta la primera ejecución
lista_actual = res["registros_ordenados"] if res else st.session_state.registros_base

# --- Barra lateral: Método Alfa ---
with st.sidebar:
    st.header("📈 Método Alfa")
    st.caption("Veces que se seleccionó cada método de ordenamiento")
    for metodo in METODOS:
        st.metric(metodo, st.session_state.alfa[metodo])
    st.metric("Rondas totales", st.session_state.rondas)
    grafica_alfa(st.session_state.alfa)
    st.caption("Los contadores son por visitante y se reinician al recargar la página.")
    with st.expander("ℹ️ ¿Cómo funciona?"):
        st.write(
            "1. Los datos se cargan en la RAM sin ordenar.\n"
            "2. El disparador elige al azar el campo a ordenar: `id_contenedor_teu` (Radix), "
            "`peso_bruto_kg` (Bucket) o `fecha_atracadero` (Quick Sort).\n"
            "3. Después elige al azar entre búsqueda binaria o lineal y mide su tiempo.\n"
            "4. Cada pulsación vuelve a empezar desde el orden original."
        )

# --- Indicador de pasos ---
p1, p2, p3 = st.columns(3)
p1.markdown(tarjeta_paso("1", "Carga a la RAM", f"{n_total:,} registros cargados", True),
            unsafe_allow_html=True)
p2.markdown(tarjeta_paso("2", "Ordenamiento",
                         f"{res['metodo']} por {res['campo']}" if res else "Pulsa el disparador",
                         res is not None), unsafe_allow_html=True)
p3.markdown(tarjeta_paso("3", "Búsqueda",
                         f"{res['tipo_busqueda']} sobre {res['campo_busqueda']}" if res
                         else "Se ejecuta tras ordenar", res is not None), unsafe_allow_html=True)

# --- Carga a RAM + disparador ---
with st.container(border=True):
    col_ok, col_t = st.columns([2, 1])
    col_ok.success(f"[ÉXITO] Se cargaron {n_total:,} registros a la memoria RAM.")
    col_t.metric("Tiempo de carga a la RAM", f"{st.session_state.tiempo_carga:,} ns")
    if res is None:
        st.warning("Los datos están **sin ordenar** (tal como vienen en el CSV). "
                   "Presiona el disparador para ordenarlos y ejecutar una búsqueda.")
    else:
        st.success(f"Datos ordenados por {res['campo']} con {res['metodo']}.")
    st.button("▶ Ejecutar disparador (ordenar + buscar)", type="primary", on_click=ejecutar_ronda)

# --- Contenido principal en pestañas ---
tab_res, tab_id, tab_reg = st.tabs(["📊 Resultados", "🔎 Consulta por ID", "📋 Registros"])

# ---------- Pestaña: Resultados ----------
with tab_res:
    if res is None:
        st.info("👆 Presiona **Ejecutar disparador** para ordenar los datos. Aquí aparecerán el "
                "benchmarking de ordenación y el de búsqueda.")
    else:
        st.subheader("Benchmarking de Ordenación")
        st.info(
            f"Se ordenaron {n_total:,} registros por el campo {res['campo']} "
            f"usando el método {res['metodo']} en {res['ns_orden']} nanosegundos. "
            f"Comparaciones: {res['comparaciones']}, Intercambios/Movimientos: {res['movimientos']}"
        )
        c1, c2, c3, c4 = st.columns(4)
        c1.metric("Campo ordenado", res["campo"])
        c2.metric("Método", res["metodo"])
        c3.metric("Tiempo (ns)", f"{res['ns_orden']:,}")
        c4.metric("Comparaciones / Movimientos",
                  f"{res['comparaciones']:,} / {res['movimientos']:,}")
        st.download_button(
            "⬇️ Descargar lista ordenada (.txt)",
            data=res["txt"],
            file_name=f"registros_ordenados_por_{res['campo']}.txt",
            mime="text/plain",
        )

        st.divider()
        st.subheader("Benchmarking de Búsqueda")
        encontrado = res["posicion"] >= 0
        st.info(
            f"Búsqueda {res['tipo_busqueda']} sobre el campo {res['campo_busqueda']} "
            f"del valor {res['objetivo']!r}: "
            + (f"encontrado en la posición {res['posicion'] + 1:,}" if encontrado
               else "no encontrado")
            + f" en {res['ns_busqueda']} nanosegundos ({res['pasos']:,} pasos)."
        )
        b1, b2, b3, b4 = st.columns(4)
        b1.metric("Tipo de búsqueda", res["tipo_busqueda"])
        b2.metric("Campo buscado", res["campo_busqueda"])
        b3.metric("Valor buscado", str(res["objetivo"]))
        b4.metric("Tiempo (ns)", f"{res['ns_busqueda']:,}")
        if res["tipo_busqueda"] == "Binaria":
            st.caption("La búsqueda binaria usa el campo que acaba de ordenarse en esta ronda.")
        else:
            st.caption("La búsqueda lineal recorre la lista secuencialmente sobre un campo elegido "
                       "al azar (clave o informativo).")

# ---------- Pestaña: Consulta por ID ----------
with tab_id:
    st.subheader("Consulta por ID de contenedor")
    ejemplo = lista_actual[0].id_contenedor_teu
    entrada = st.text_input("Escribe el id_contenedor_teu a buscar",
                            placeholder=f"Ejemplo: {ejemplo}").strip()
    if entrada:
        if not (entrada.isascii() and entrada.isdigit()):
            st.error("El ID debe ser un número entero (solo dígitos).")
        else:
            id_buscado = int(entrada)
            # Binaria solo si la lista quedó ordenada por este mismo campo en la ronda actual;
            # en cualquier otro caso (incluida la lista aún sin ordenar) se usa la lineal.
            if res is not None and res["campo"] == "id_contenedor_teu":
                tipo_id = "Binaria"
                pos_id, ns_id, pasos_id = busqueda_binaria(
                    lista_actual, "id_contenedor_teu", id_buscado)
            else:
                tipo_id = "Lineal (secuencial)"
                pos_id, ns_id, pasos_id = busqueda_lineal(
                    lista_actual, "id_contenedor_teu", id_buscado)

            i1, i2, i3, i4 = st.columns(4)
            i1.metric("Tipo de búsqueda", tipo_id)
            i2.metric("Tiempo (ns)", f"{ns_id:,}")
            i3.metric("Pasos", f"{pasos_id:,}")
            i4.metric("Posición", f"{pos_id + 1:,}" if pos_id >= 0 else "—")

            if pos_id >= 0:
                st.success(f"Contenedor {id_buscado} encontrado con búsqueda {tipo_id}.")
                reg = lista_actual[pos_id]
                st.dataframe(
                    pd.DataFrame({"Campo": TODOS_LOS_CAMPOS,
                                  "Valor": [valor_texto(reg, c) for c in TODOS_LOS_CAMPOS]}),
                    hide_index=True,
                )
            else:
                st.warning(f"No existe ningún contenedor con id_contenedor_teu = {id_buscado}.")
    st.caption("Si en esta ronda la lista se ordenó por id_contenedor_teu se usa búsqueda binaria; "
               "si no (o si aún no se ordena), búsqueda lineal (secuencial), porque la binaria "
               "exige la lista ordenada por el campo buscado.")

# ---------- Pestaña: Registros ----------
with tab_reg:
    st.subheader("Vista de los registros (primeros 30 y últimos 30)")
    if res is None:
        st.caption("Orden original del CSV (sin ordenar).")
        mostrar_30_30(st.session_state.registros_base)
    else:
        sub_orden, sub_csv = st.tabs(
            [f"Después de ordenar por {res['campo']}", "Orden original del CSV (sin ordenar)"])
        with sub_orden:
            mostrar_30_30(res["registros_ordenados"])
        with sub_csv:
            mostrar_30_30(st.session_state.registros_base)

st.caption("Datos: puertos y fechas reales de SEMAR; pesos, costos, navieras y estatus simulados.")
