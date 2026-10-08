-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_resourceInvestment_lowerSemicontinuous
-- name    : ProjSchedTW.ObjectiveClasses.resourceInvestment_lowerSemicontinuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:39.521985+00:00
-- url     : https://prove2.me/theorems/0d354b0c-f2e1-4f9a-9655-e558e2675d16
-- title:
--   Proposition 3.3.6 — the resource investment objective is lower semicontinuous
-- statement:
--   Let $c_k\ge 0$ ($k\in\mathcal R$) and let $f(S)=\sum_{k\in\mathcal R}c_k\max_{t}r_k(S,t)$ be the resource investment objective. Then $f$ is lower semicontinuous on $\mathbb R^{n+2}_{\ge 0}$:
--   $$f(S)\ \le\ \liminf_{S'\to S}f(S')\qquad\text{for all } S\in\mathbb R^{n+2}_{\ge 0}.$$
--
--   The function is discontinuous (removing an overlap of two activities can lower the peak resource usage), so lower semicontinuity is what guarantees that it attains its minimum on the compact feasible region.
--
--   **Formalization Note** The limit is taken within the nonnegative orthant (Mathlib's `LowerSemicontinuousOn`), and the maximum over $t$ is taken over all $t\ge 0$. With the book's literal range $0\le t\le\bar d$ the statement would fail at points of the orthant where an activity starts exactly at $\bar d$; for feasible schedules the two ranges agree.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 230, Proposition 3.3.6 (objective from p. 203, Definition 3.3.3 on p. 227)

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- Proposition 3.3.6 (p. 230): the resource investment objective `∑ c_k max r_kt` is lower
semicontinuous (Definition 3.3.3, on `ℝ^{n+2}_{≥0}`). The peak `max_t r_k(S, t)` is taken over
all `t ≥ 0` (`peakUsage`); with the book's literal range `0 ≤ t ≤ d̄` the statement fails on the
orthant (an activity starting exactly at `d̄` stops counting when shifted right), while on `𝒮` the
two ranges agree. -/
theorem resourceInvestment_lowerSemicontinuous {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (c : K → ℝ) (hc : ∀ k, 0 ≤ c k) :
    IsLowerSemicontinuous (resourceInvestment P c) := by sorry

end ProjSchedTW.ObjectiveClasses
