-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_centralisation_optimum
-- name    : TeamDelegation.Optimal.centralisation_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:20.497005+00:00
-- url     : https://prove2.me/theorems/cf68f029-2906-49b6-9007-c16c004169bd
-- title:
--   Equation (9): optimal centralised success bonus
-- statement:
--   Let the model satisfy its standing assumptions and Assumption 1, with A's method-2 adoption cost at least its method-1 cost. The equal bonus
--
--   $$w^{\mathrm{cent}}=\frac{e}{p_2-(1-\delta)p_1-\delta p_0}$$
--
--   implements work by both agents under centralisation. For every pair of nonnegative success bonuses that implements the same desired path using a stage-game Nash punishment, each bonus is at least $w^{\mathrm{cent}}$.
--
--   Thus equation (9) identifies the least possible centralised wage cost within the paper's grim-trigger equilibrium class.
--
--   **Formalization Note** Punishments may be mixed; the centralised feasible set fixes the correct method in each state.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 14 (PDF 15), §4.1 Step Two, equation (9) and following paragraph

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- §4.1, equation (9): the equal centralised bonus implements the desired path,
and no lower success bonus can implement it for either agent. -/
theorem centralisation_optimum (P : Params) (C : Costs)
    (hS : P.Standing) (hA1 : P.Assumption1) (hC : C.Standing) :
    Implements P C .cent (wcent P) (wcent P) ∧
      ∀ wA wB : ℝ, Implements P C .cent wA wB →
        wcent P ≤ wA ∧ wcent P ≤ wB := by sorry

end TeamDelegation.Optimal
