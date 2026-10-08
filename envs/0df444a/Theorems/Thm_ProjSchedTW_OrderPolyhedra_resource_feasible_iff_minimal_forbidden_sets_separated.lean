-- Prove2me | Theorems.Thm_ProjSchedTW_OrderPolyhedra_resource_feasible_iff_minimal_forbidden_sets_separated
-- name    : ProjSchedTW.OrderPolyhedra.resource_feasible_iff_minimal_forbidden_sets_separated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T15:29:58.322141+00:00
-- url     : https://prove2.me/theorems/d0d5aeb8-b68d-4aa7-8de1-408c0a662367
-- title:
--   Bartusch et al.'s criterion — a schedule is resource-feasible iff every minimal forbidden set has a precedence pair
-- statement:
--   Consider a project satisfying the standing assumptions, and let $S$ be a schedule ($S_0 = 0$, $S_i \ge 0$). Then $S$ is resource-feasible, that is $r_k(S,t) \le R_k$ for all $k \in \mathcal R$ and $t \ge 0$, if and only if
--   $$\forall F \in \mathcal F\ \ \exists\, i, j \in F,\ i \ne j:\quad S_j \ge S_i + p_i,$$
--   where $\mathcal F$ is the set of minimal forbidden sets.
--
--   The book quotes this criterion from Bartusch, Möhring & Radermacher (1988) in the proof of Theorem 2.3.10; it is the step that turns resource feasibility into finitely many disjunctive precedence conditions.
--
--   **Formalization Note** Resource constraints are required for every $t \ge 0$ (not only up to $\bar d$); the schedule need not be time-feasible.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 35–36, proof of Theorem 2.3.10 (criterion of Bartusch et al. 1988)

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

namespace ProjSchedTW.OrderPolyhedra

/-- Bartusch et al.'s resource-feasibility criterion (proof of Theorem 2.3.10, pp. 35–36):
a schedule `S` is resource-feasible exactly if for every minimal forbidden set `F` there are
two distinct activities `i, j ∈ F` with `S_j ≥ S_i + p_i`. -/
theorem resource_feasible_iff_minimal_forbidden_sets_separated {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    P.IsResourceFeasible S ↔
      ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F →
        ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧ S i + (P.p i : ℝ) ≤ S j := by sorry

end ProjSchedTW.OrderPolyhedra
