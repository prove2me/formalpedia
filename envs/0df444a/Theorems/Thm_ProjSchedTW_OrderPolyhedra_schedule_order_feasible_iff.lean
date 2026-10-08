-- Prove2me | Theorems.Thm_ProjSchedTW_OrderPolyhedra_schedule_order_feasible_iff
-- name    : ProjSchedTW.OrderPolyhedra.schedule_order_feasible_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T15:30:06.282873+00:00
-- url     : https://prove2.me/theorems/eb3076df-fdca-4c91-aed8-b353ec7d5caa
-- title:
--   Proposition 2.3.6 — the schedule-induced strict order O(S) is feasible iff S is feasible
-- statement:
--   Consider a project satisfying the standing assumptions, and let $S$ be a time-feasible schedule. Let $O(S) = \{(i,j) \mid i \ne j,\ S_j \ge S_i + p_i\}$ be the schedule-induced strict order. Then
--   $$O(S) \text{ is a feasible strict order} \iff S \in \mathcal S.$$
--
--   Together with $S \in \mathcal S_T(O(S))$, this shows that the feasible schedules are exactly the time-feasible schedules whose induced order is feasible, which is the step behind the basic structural theorem (Theorem 2.3.7).
--
--   **Formalization Note** "Feasible strict order" includes being a strict order; that $O(S)$ is asymmetric uses $S_{n+1} > 0$, which holds for time-feasible $S$ by the standing assumptions ($n \ge 1$ and a path from a real activity $i$ to $n+1$ of length $\ge p_i > 0$).
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 32, Proposition 2.3.6

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

namespace ProjSchedTW.OrderPolyhedra

/-- Proposition 2.3.6 (p. 32): the strict order `O(S)` induced by a time-feasible schedule `S`
is feasible if and only if the schedule `S` is feasible. -/
theorem schedule_order_feasible_iff {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : P.IsTimeFeasible S) :
    P.IsFeasibleOrder (P.scheduleOrder S) ↔ P.IsFeasible S := by sorry

end ProjSchedTW.OrderPolyhedra
