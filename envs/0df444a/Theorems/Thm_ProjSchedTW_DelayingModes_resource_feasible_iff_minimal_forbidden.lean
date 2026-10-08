-- Prove2me | Theorems.Thm_ProjSchedTW_DelayingModes_resource_feasible_iff_minimal_forbidden
-- name    : ProjSchedTW.DelayingModes.resource_feasible_iff_minimal_forbidden
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T22:40:44.881974+00:00
-- url     : https://prove2.me/theorems/a81bf918-9995-48f8-a95b-271d6295e7a7
-- title:
--   Proof of Theorem 2.3.10, p. 35 — Bartusch et al.'s criterion for resource-feasibility
-- statement:
--   Let $S$ be a schedule of a project ($S_0=0$, $S_i\ge0$). Then $S$ is resource-feasible, i.e. $r_k(S,t)\le R_k$ for every resource $k$ and every $t\ge0$, if and only if every minimal forbidden set $F$ contains two distinct activities $i,j$ with
--   $$S_j\ge S_i+p_i.$$
--
--   In words: $S$ respects the resource capacities exactly when, in every minimal forbidden set, some activity starts only after another has completed, so that the activities of $F$ are never all in progress at the same time. The criterion is quoted from Bartusch, Möhring and Radermacher (1988) in the proof of Theorem 2.3.10 and is the fact the proof of Theorem 2.5.7 draws from Theorem 2.3.10.
--
--   **Formalization Note.** Resource constraints are required for all $t\ge0$; with the literal cut-off $t\le\bar d$ of (2.1.4) the "only if" direction would fail for schedules whose conflicts lie after $\bar d$. The standing assumptions of the model (in particular $p_i>0$ for real activities and $r_{0k}=r_{n+1,k}=0$) are hypotheses.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 35, proof of Theorem 2.3.10, Bartusch et al.'s criterion

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

namespace ProjSchedTW.DelayingModes

theorem resource_feasible_iff_minimal_forbidden {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    P.IsResourceFeasible S ↔
      ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F →
        ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧ S i + P.p i ≤ S j := by sorry

end ProjSchedTW.DelayingModes
