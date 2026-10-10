-- Prove2me | Theorems.Thm_SecondLawThermo_clausius_iff_kelvin
-- name    : SecondLawThermo.clausius_iff_kelvin
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:31.220718+00:00
-- url     : https://prove2.me/theorems/96f62a61-873c-447d-9f1a-87f81aa7df28
-- title:
--   Equivalence of the Clausius and the Kelvin statements
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\Theta$ have at least two elements and let $\mathcal C$ be a convex cone of realizable cycles admitting a Carnot engine between every pair of reservoirs at different temperatures. Then
--
--   $$\text{Clausius}(\mathcal C)\iff\text{Kelvin}(\mathcal C).$$
--
--   This is the article's assertion that the two classical statements of the second law — Clausius's "heat can never pass from a colder to a warmer body without some other change" and Kelvin's "it is impossible for any system to operate in a thermodynamic cycle and deliver a net amount of energy by work to its surroundings while receiving energy by heat transfer from a single thermal reservoir" — say the same thing.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; section "Equivalence of the Clausius and the Kelvin statements": "The Clausius and the Kelvin statements have been shown to be equivalent."

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem clausius_iff_kelvin {Θ : Type*} [LinearOrder Θ] [Nontrivial Θ] (𝒞 : Set (Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCarnot : CarnotEnginesExist 𝒞) :
    ClausiusStatement 𝒞 ↔ KelvinStatement 𝒞 := by sorry

end SecondLawThermo
