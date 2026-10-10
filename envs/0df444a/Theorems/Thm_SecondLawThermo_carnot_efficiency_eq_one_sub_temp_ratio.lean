-- Prove2me | Theorems.Thm_SecondLawThermo_carnot_efficiency_eq_one_sub_temp_ratio
-- name    : SecondLawThermo.carnot_efficiency_eq_one_sub_temp_ratio
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:30.542971+00:00
-- url     : https://prove2.me/theorems/b105b97d-1707-40bd-9c2f-1b3183bd0e11
-- title:
--   Carnot efficiency on the thermodynamic scale: $\eta = 1 - T_\mathrm{C}/T_\mathrm{H}$
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $T:\Theta\to\mathbb R$ be a scale for which every Carnot engine $e$ between reservoirs $k<h$ satisfies $|e(k)|/|e(h)|=T(k)/T(h)$. Then every such Carnot engine has efficiency
--
--   $$\eta(e)=1-\frac{T(k)}{T(h)}.$$
--
--   This combines equation (1) with the definition of the thermodynamic temperature scale: on that scale the efficiency of a reversible engine depends on the two reservoirs only through the ratio of their thermodynamic temperatures.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; sections "Thermodynamic temperature" (eq. (1) and $f(T_2,T_3)=T_3^*/T_2^*$)

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem carnot_efficiency_eq_one_sub_temp_ratio {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ))
    (T : Θ → ℝ)
    (hT : ∀ (h k : Θ) (e : Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = T k / T h)
    (h k : Θ) (hkh : k < h) (e : Cycle Θ) (he : IsCarnotEngine 𝒞 e h k) :
    efficiency e h = 1 - T k / T h := by sorry

end SecondLawThermo
