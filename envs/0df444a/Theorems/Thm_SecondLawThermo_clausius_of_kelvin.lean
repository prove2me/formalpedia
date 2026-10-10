-- Prove2me | Theorems.Thm_SecondLawThermo_clausius_of_kelvin
-- name    : SecondLawThermo.clausius_of_kelvin
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:01.660268+00:00
-- url     : https://prove2.me/theorems/8fb8ca36-8601-4ea5-8cbb-dfd44b5dfd13
-- title:
--   The Kelvin statement implies the Clausius statement
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\mathcal C$ be a convex cone of realizable cycles admitting a Carnot engine between every pair of reservoirs at different temperatures. If the Kelvin statement holds for $\mathcal C$, then so does the Clausius statement:
--
--   $$\text{Kelvin}(\mathcal C)\implies\text{Clausius}(\mathcal C).$$
--
--   This is one half of the article's claim that "the Clausius and the Kelvin statements have been shown to be equivalent": a device transferring heat from a cold to a hot reservoir with no other change can be combined with a Carnot engine so that the composite exchanges heat with one reservoir only and delivers positive work.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; sections "Clausius statement", "Kelvin statements", "Equivalence of the Clausius and the Kelvin statements"

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem clausius_of_kelvin {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ)) (h𝒞 : IsCycleCone 𝒞)
    (hCarnot : CarnotEnginesExist 𝒞) (hK : KelvinStatement 𝒞) :
    ClausiusStatement 𝒞 := by sorry

end SecondLawThermo
