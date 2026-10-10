-- Prove2me | Theorems.Thm_SecondLawThermo_exists_temperature_scale_of_mul
-- name    : SecondLawThermo.exists_temperature_scale_of_mul
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:41.131145+00:00
-- url     : https://prove2.me/theorems/fd17902a-94b0-4b1a-b765-a67d05bcfd90
-- title:
--   A multiplicative two-variable function is a ratio of a positive function of one variable
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\Theta$ be linearly ordered and let $f:\Theta\times\Theta\to\mathbb R$ be positive on ordered pairs, $f(h,k)>0$ for $k<h$, and multiplicative in the sense that
--
--   $$f(T_1,T_3)=f(T_1,T_2)\,f(T_2,T_3)\qquad (T_3<T_2<T_1).$$
--
--   Then for every $T_0\in\Theta$ and every $a>0$ there is a function $T:\Theta\to\mathbb R$ with $T>0$ everywhere, $T(T_0)=a$, and
--
--   $$f(h,k)=\frac{T(k)}{T(h)}\qquad (k<h).$$
--
--   This is the step by which the article converts the composition law for the reversible heat ratio into a temperature scale, with $T_0$ the triple point of water and $a=273.16$: "Therefore, if thermodynamic temperature $T^*$ is defined by $T^*=273.16\,\mathrm K\cdot f(T_1,T)$ then the function $f$, viewed as a function of thermodynamic temperatures, is simply $f(T_2,T_3)=T_3^*/T_2^*$."
--
--   **Formalization Note** The statement is purely about the functional equation, with no thermodynamic content; the reference temperature $T_0$ need not be extremal, so the scale is built from $f(T_0,\cdot)$ below $T_0$ and from $1/f(\cdot,T_0)$ above it.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; section "Thermodynamic temperature": the passage from $f(T_1,T_3)=f(T_1,T_2)f(T_2,T_3)$ to $T^*=273.16\,\mathrm{K}\cdot f(T_1,T)$ and $f(T_2,T_3)=T_3^*/T_2^*$

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem exists_temperature_scale_of_mul {Θ : Type*} [LinearOrder Θ] (f : Θ → Θ → ℝ)
    (hf_pos : ∀ h k : Θ, k < h → 0 < f h k)
    (hf_mul : ∀ T₁ T₂ T₃ : Θ, T₃ < T₂ → T₂ < T₁ → f T₁ T₃ = f T₁ T₂ * f T₂ T₃)
    (T₀ : Θ) (a : ℝ) (ha : 0 < a) :
    ∃ T : Θ → ℝ, (∀ t, 0 < T t) ∧ T T₀ = a ∧ ∀ h k : Θ, k < h → f h k = T k / T h := by sorry

end SecondLawThermo
