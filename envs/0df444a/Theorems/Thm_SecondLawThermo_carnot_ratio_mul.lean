-- Prove2me | Theorems.Thm_SecondLawThermo_carnot_ratio_mul
-- name    : SecondLawThermo.carnot_ratio_mul
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:56.348248+00:00
-- url     : https://prove2.me/theorems/4dbf97e8-5e63-4b52-a433-eb10a21058cb
-- title:
--   Composition law $f(T_1,T_3)=f(T_1,T_2)f(T_2,T_3)$ for the Carnot heat ratio
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\mathcal C$ be a convex cone of realizable cycles satisfying the Clausius statement and let $T_3<T_2<T_1$ be three reservoir temperatures. Let $e_1$ be a Carnot engine between $T_1$ and $T_3$, $e_2$ one between $T_1$ and $T_2$, and $e_3$ one between $T_2$ and $T_3$. Then the heat ratios compose:
--
--   $$\frac{|e_1(T_3)|}{|e_1(T_1)|}=\frac{|e_2(T_2)|}{|e_2(T_1)|}\cdot\frac{|e_3(T_3)|}{|e_3(T_2)|}.$$
--
--   Writing $f(T_{\mathrm H},T_{\mathrm C})=|q_{\mathrm C}|/|q_{\mathrm H}|$ for the (substance-independent) ratio of a reversible engine, this is the article's identity $f(T_1,T_3)=f(T_1,T_2)\,f(T_2,T_3)$: a reversible engine between $T_1$ and $T_3$ has the same efficiency as the two-cycle engine passing through an intermediate reservoir at $T_2$, the heat $q_2$ passing through the intermediate reservoir without loss.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; section "Thermodynamic temperature": the derivation of $f(T_1,T_3)=f(T_1,T_2)f(T_2,T_3)$

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem carnot_ratio_mul {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (T₁ T₂ T₃ : Θ)
    (h₃₂ : T₃ < T₂) (h₂₁ : T₂ < T₁) (e₁ e₂ e₃ : Cycle Θ)
    (he₁ : IsCarnotEngine 𝒞 e₁ T₁ T₃) (he₂ : IsCarnotEngine 𝒞 e₂ T₁ T₂)
    (he₃ : IsCarnotEngine 𝒞 e₃ T₂ T₃) :
    |e₁ T₃| / |e₁ T₁| = (|e₂ T₂| / |e₂ T₁|) * (|e₃ T₃| / |e₃ T₂|) := by sorry

end SecondLawThermo
