-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_pseudostable_iff_local_extreme
-- name    : ProjSchedTW.StableSchedules.pseudostable_iff_local_extreme
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:14:31.813027+00:00
-- url     : https://prove2.me/theorems/bc5560f1-4b23-4380-b833-e03bbbca865c
-- title:
--   Lemma 3.2.8 — pseudostable schedules are the local extreme points of the feasible region
-- statement:
--   Let $\mathcal S$ be the feasible region of a project. A schedule $S$ is pseudostable if and only if $S$ is a local extreme point of $\mathcal S$:
--   $$S\in\mathcal{PSS}\iff S\text{ lies on no line segment that joins two other points of }\mathcal S\text{ and lies entirely in }\mathcal S.$$
--
--   Pseudostable means feasible with no pair of opposite order-monotone shifts from $S$. The lemma is the geometric form of that definition, and part (d) of Theorem 3.2.10 is proved from it.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 210, Lemma 3.2.8

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.StableSchedules

/-- Lemma 3.2.8 (p. 210). A schedule `S` is pseudostable iff `S` is a local extreme point of the
feasible region `𝒮`. -/
theorem pseudostable_iff_local_extreme {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) :
    IsPseudostable P S ↔ IsLocalExtremePoint (feasibleSet P) S := by sorry

end ProjSchedTW.StableSchedules
