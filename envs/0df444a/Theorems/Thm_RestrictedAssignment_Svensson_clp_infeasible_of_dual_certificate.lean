-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_clp_infeasible_of_dual_certificate
-- name    : RestrictedAssignment.Svensson.clp_infeasible_of_dual_certificate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:27:24.483183+00:00
-- url     : https://prove2.me/theorems/08a68c13-ef8f-4840-a0a7-7de1b0c8f206
-- title:
--   Proof of Lemma 3.7 — a dual solution with $\sum_i y_i < \sum_j z_j$ certifies infeasibility of [C-LP]
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment and $T \in \mathbb R$ a target makespan. If $(y, z)$ is a feasible solution of the dual of [C-LP], that is $y, z \ge 0$ and $y_i \ge \sum_{j \in C} z_j$ for every machine $i$ and every configuration $C \in \mathcal C(i,T)$, and
--   $$
--   \sum_{i \in M} y_i < \sum_{j \in J} z_j,
--   $$
--   then [C-LP] is infeasible for target makespan $T$.
--
--   In the paper this appears as the observation that such a dual solution can be scaled to make the dual objective arbitrarily negative, so the dual is unbounded and the primal infeasible. It is the step that turns Claims 4.7 and 4.8 into Lemma 4.6.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 8, proof of Lemma 3.7 (reused on p. 15, proof of Lemma 4.6)

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 8, proof of Lemma 3.7 (used again on p. 15): a feasible
solution `(y, z)` of the dual of [C-LP] with `∑_i y_i < ∑_j z_j` certifies that [C-LP] is
infeasible. -/
theorem clp_infeasible_of_dual_certificate {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (y : M → ℝ) (z : J → ℝ)
    (hdual : CLPDualFeasible Γ p T y z) (hneg : ∑ i, y i < ∑ j, z j) :
    ¬ CLPFeasible Γ p T := by sorry

end RestrictedAssignment.Svensson
