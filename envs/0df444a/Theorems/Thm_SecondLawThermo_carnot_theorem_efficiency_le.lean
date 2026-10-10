-- Prove2me | Theorems.Thm_SecondLawThermo_carnot_theorem_efficiency_le
-- name    : SecondLawThermo.carnot_theorem_efficiency_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:00.71599+00:00
-- url     : https://prove2.me/theorems/a6668366-9713-4490-abc3-4784ed1126b3
-- title:
--   Carnot's theorem: no engine beats a Carnot engine between the same reservoirs
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\mathcal C$ be a convex cone of realizable cycles satisfying the Clausius statement, let $k<h$, and let $e$ be a Carnot engine between $h$ and $k$. Then every realizable cycle $c$ operating between $h$ and $k$ and absorbing $c(h)>0$ from the hot reservoir satisfies
--
--   $$\eta(c)=\frac{W(c)}{c(h)}\ \le\ \frac{W(e)}{e(h)}=\eta(e).$$
--
--   This is the quantitative content of Carnot's theorem: the efficiency of any heat engine operating between two given reservoirs is at most that of a reversible (Carnot) engine operating between the same two reservoirs.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; section "Carnot's theorem": "All irreversible heat engines between two heat reservoirs are less efficient than a Carnot engine operating between the same reservoirs."

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem carnot_theorem_efficiency_le {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (h k : Θ) (hkh : k < h)
    (e : Cycle Θ) (he : IsCarnotEngine 𝒞 e h k) (c : Cycle Θ) (hc : c ∈ 𝒞)
    (hcb : OperatesBetween c h k) (hqH : 0 < c h) :
    efficiency c h ≤ efficiency e h := by sorry

end SecondLawThermo
