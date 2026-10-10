-- Prove2me | Theorems.Thm_SecondLawThermo_thermodynamic_temperature
-- name    : SecondLawThermo.thermodynamic_temperature
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:07.96743+00:00
-- url     : https://prove2.me/theorems/79732920-55bf-49dd-87f8-bc20491793e2
-- title:
--   Existence and uniqueness of the thermodynamic temperature scale
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement (goal).** Let $\mathcal C$ be a convex cone of realizable cycles which satisfies the Clausius statement and admits a Carnot engine between every pair of reservoirs at different temperatures, and let $T_0$ be a reference reservoir (the triple point of water). Then there is a function $T:\Theta\to\mathbb R$ with
--
--   1. $T(t)>0$ for every $t$;
--   2. $T(T_0)=273.16$;
--   3. for all $k<h$, every Carnot engine $e$ between $h$ and $k$ satisfies $\dfrac{|e(k)|}{|e(h)|}=\dfrac{T(k)}{T(h)}$;
--
--   and $T$ is the only function with these three properties.
--
--   This is the article's claim that "the second law allows a distinguished temperature scale, which defines an absolute, thermodynamic temperature, independent of the properties of any particular reference thermometric body": from the Clausius statement alone, the ratio of heats exchanged by *any* reversible engine between two reservoirs is a ratio of two numbers attached to the reservoirs themselves, normalized by the Kelvin convention $273.16$ at the triple point of water.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; sections "Relating the second law to the definition of temperature" and "Thermodynamic temperature" (through $T^*=273.16\,\mathrm{K}\cdot f(T_1,T)$, $T_1^*=273.16\,\mathrm{K}$)

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem thermodynamic_temperature {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (hCarnot : CarnotEnginesExist 𝒞)
    (T₀ : Θ) :
    ∃ T : Θ → ℝ, (∀ t, 0 < T t) ∧ T T₀ = 273.16 ∧
      (∀ (h k : Θ) (e : Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
        |e k| / |e h| = T k / T h) ∧
      ∀ T' : Θ → ℝ, (∀ t, 0 < T' t) → T' T₀ = 273.16 →
        (∀ (h k : Θ) (e : Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
          |e k| / |e h| = T' k / T' h) → T' = T := by sorry

end SecondLawThermo
