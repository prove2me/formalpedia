-- Prove2me | Theorems.Thm_SecondLawThermo_efficiency_eq_one_sub_abs_ratio
-- name    : SecondLawThermo.efficiency_eq_one_sub_abs_ratio
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:35.090062+00:00
-- url     : https://prove2.me/theorems/73582d4e-31c1-45c4-a946-8732a9ab3c59
-- title:
--   Efficiency of a heat engine: $\eta = 1 - |q_\mathrm{C}|/|q_\mathrm{H}|$
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $c$ be a cycle operating between two distinct reservoirs $h\ne k$, absorbing $q_{\mathrm H}=c(h)>0$ from the hot one and rejecting $q_{\mathrm C}=c(k)<0$ to the cold one. Then
--
--   $$\eta=\frac{|W_{\mathrm n}|}{q_{\mathrm H}}=\frac{q_{\mathrm H}+q_{\mathrm C}}{q_{\mathrm H}}=1-\frac{|q_{\mathrm C}|}{|q_{\mathrm H}|}.$$
--
--   This is equation (1) of the article's section *Thermodynamic temperature*. It records that the efficiency of a two-reservoir engine depends only on the ratio $|q_{\mathrm C}|/|q_{\mathrm H}|$, which is what makes that ratio, rather than the efficiency, the natural carrier of the temperature dependence.
--
--   **Formalization Note** No realizability assumption is used: the identity is the first law for a cycle supported on two reservoirs.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; section "Thermodynamic temperature", equation (1)

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem efficiency_eq_one_sub_abs_ratio {Θ : Type*} (c : Cycle Θ) (h k : Θ) (hhk : h ≠ k)
    (hc : OperatesBetween c h k) (hqH : 0 < c h) (hqC : c k < 0) :
    efficiency c h = 1 - |c k| / |c h| := by sorry

end SecondLawThermo
