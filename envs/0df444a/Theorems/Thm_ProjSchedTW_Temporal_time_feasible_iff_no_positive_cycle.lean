-- Prove2me | Theorems.Thm_ProjSchedTW_Temporal_time_feasible_iff_no_positive_cycle
-- name    : ProjSchedTW.Temporal.time_feasible_iff_no_positive_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T14:34:56.224968+00:00
-- url     : https://prove2.me/theorems/66e17533-5410-4a3c-a6a1-195f13c517aa
-- title:
--   Theorem 1.3.3 — a time-feasible schedule exists iff the project network has no cycle of positive length
-- statement:
--   Let a project with AoN network $N$ on $V=\{0,1,\dots,n+1\}$ satisfy the standing assumption: for every node $i$ there are a path from $0$ to $i$ of nonnegative length and a path from $i$ to $n+1$ of length at least $p_i$. Then
--   $$\mathcal S_T\ne\emptyset\iff N\text{ contains no cycle of positive length},$$
--   where $\mathcal S_T$ is the set of schedules $S$ ($S_0=0$, $S_i\ge 0$, real start times) satisfying the temporal constraints $S_j-S_i\ge\delta_{ij}$ for all $\langle i,j\rangle\in E$.
--
--   This is the basic feasibility criterion of temporal project scheduling with minimum and maximum time lags: the temporal constraints are consistent exactly when the time lags around every cycle do not add up to a positive amount.
--
--   **Formalization Note.** The standing assumption of p. 8 is a hypothesis; without it the statement is false (an arc $\langle i,0\rangle$ with $\delta_{i0}>0$ forces $S_i<0$ with no cycle involved). Arc weights are arbitrary integers, so maximum time lags (negative weights) and cycles are allowed. Cycles are simple cycles; the statement is equivalent to the one for closed walks.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 10, Theorem 1.3.3 (with Definition 1.3.1, p. 10, and the path property of AoN networks, p. 8)

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_Project

namespace ProjSchedTW.Temporal

/-- Theorem 1.3.3 (p. 10): there is a time-feasible schedule for a project if and only if the
corresponding AoN network `N` does not contain any cycle of positive length. The standing
property of AoN networks (p. 8) is a hypothesis. -/
theorem time_feasible_iff_no_positive_cycle {n : ℕ} (P : Project n)
    (hP : P.StandingAssumption) :
    (∃ S : Fin (n + 2) → ℝ, IsTimeFeasible P.N S) ↔ ¬ HasPositiveCycle P.N := by sorry

end ProjSchedTW.Temporal
