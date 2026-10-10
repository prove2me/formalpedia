-- Prove2me | Theorems.Thm_SecondLawThermo_kelvin_of_clausius
-- name    : SecondLawThermo.kelvin_of_clausius
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:30.584973+00:00
-- url     : https://prove2.me/theorems/f00f12ea-04d1-4ddd-a7a0-b53e221a3a32
-- title:
--   The Clausius statement implies the Kelvin statement
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\Theta$ have at least two elements and let $\mathcal C$ be a convex cone of realizable cycles admitting a Carnot engine between every pair of reservoirs at different temperatures. If the Clausius statement holds for $\mathcal C$, then so does the Kelvin statement:
--
--   $$\text{Clausius}(\mathcal C)\implies\text{Kelvin}(\mathcal C).$$
--
--   This is the direction the article argues explicitly: an engine draining heat from a single reservoir and converting it entirely into work, paired with a reversed Carnot engine, has as its net and sole effect the transfer of heat from a cooler to a hotter reservoir.
--
--   **Formalization Note** At least two reservoir temperatures must exist for the Clausius statement to have any content; with a single temperature it holds vacuously while the Kelvin statement can fail.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; section "Equivalence of the Clausius and the Kelvin statements"

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem kelvin_of_clausius {Θ : Type*} [LinearOrder Θ] [Nontrivial Θ] (𝒞 : Set (Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCarnot : CarnotEnginesExist 𝒞) (hCl : ClausiusStatement 𝒞) :
    KelvinStatement 𝒞 := by sorry

end SecondLawThermo
