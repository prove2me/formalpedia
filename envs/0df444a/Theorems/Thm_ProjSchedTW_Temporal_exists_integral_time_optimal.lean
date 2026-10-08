-- Prove2me | Theorems.Thm_ProjSchedTW_Temporal_exists_integral_time_optimal
-- name    : ProjSchedTW.Temporal.exists_integral_time_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:34:42.640203+00:00
-- url     : https://prove2.me/theorems/fc0af39d-c153-4ae6-9327-237cba298d84
-- title:
--   Remark 1.3.2 — if a time-feasible schedule exists, an integer-valued time-optimal schedule exists
-- statement:
--   Let a project with AoN network $N$ (integer arc weights $\delta_{ij}$) be given, and suppose the set $\mathcal S_T$ of time-feasible schedules is nonempty. Then there is a time-optimal schedule with integer start times: some $S\in\mathcal S_T$ with $S_i\in\mathbb Z$ for all $i\in V$ and
--   $$S_{n+1}\ \le\ S'_{n+1}\qquad\text{for all } S'\in\mathcal S_T.$$
--
--   This is what justifies treating time as discrete: the linear program (1.3.1) of minimizing the project duration has an integral optimal solution, so restricting start times to $\mathbb Z_{\ge 0}$ loses nothing.
--
--   **Formalization Note.** The second sentence of Remark 1.3.2 (the schedule remains optimal when $S_i\ge 0$ is replaced by $S_i\in\mathbb Z_{\ge0}$) is an immediate consequence of this statement, since integral schedules are schedules, and is not stated separately.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 10, Remark 1.3.2

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_Project

namespace ProjSchedTW.Temporal

/-- Remark 1.3.2 (p. 10): if the set `S_T` of time-feasible schedules is nonempty, there is an
integer-valued time-optimal schedule. -/
theorem exists_integral_time_optimal {n : ℕ} (P : Project n)
    (hST : ∃ S : Fin (n + 2) → ℝ, IsTimeFeasible P.N S) :
    ∃ S : Fin (n + 2) → ℝ, IsTimeOptimal P.N S ∧ ∀ i, ∃ z : ℤ, S i = z := by sorry

end ProjSchedTW.Temporal
