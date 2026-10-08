-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_exists_active_optimal
-- name    : ProjSchedTW.ActiveSchedules.exists_active_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T16:05:57.414587+00:00
-- url     : https://prove2.me/theorems/d8cb7b67-dad5-4f06-8681-73964d4abde9
-- title:
--   Remark 2.4.10 (a) — if the feasible region is nonempty, some active schedule is optimal
-- statement:
--   Suppose the feasible region $\mathcal S$ of the project is nonempty. Then there is a schedule $S$ that
--
--   1. is a minimal point of $\mathcal S$,
--   2. is active, and
--   3. is optimal: $S\in\mathcal S$ and $S_{n+1}\le S'_{n+1}$ for all $S'\in\mathcal S$.
--
--   In short, $$\mathcal S\neq\emptyset\ \Longrightarrow\ \mathcal{AS}\cap\mathcal{OS}\neq\emptyset.$$
--
--   This is why exact methods may restrict the search to active (and hence to quasiactive) schedules.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 44, Remark 2.4.10 (a)

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- Remark 2.4.10 (a) (p. 44): if `𝒮 ≠ ∅`, some minimal point of `𝒮` (and thus an active
schedule) is an optimal schedule. -/
theorem exists_active_optimal {n : ℕ} {K : Type} (P : Project n K)
    (h : (feasibleSet P).Nonempty) :
    ∃ S : Fin (n + 2) → ℝ, Minimal (· ∈ feasibleSet P) S ∧ IsActive P S ∧ IsOptimal P S := by sorry

end ProjSchedTW.ActiveSchedules
