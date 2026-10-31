-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_surplus_implies_collusion_proof
-- name    : TeamDelegation.Optimal.surplus_implies_collusion_proof
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:28.719026+00:00
-- url     : https://prove2.me/theorems/c07d37df-d643-45d9-8685-9cdc59efbe4d
-- title:
--   Section 7: maximal joint surplus excludes Pareto collusion
-- statement:
--   Consider delegation at any two success bonuses. If in each state both agents working with the correct method maximises their total expected one-period payoff over every feasible pure stage outcome, then no state-contingent probability distribution over feasible joint outcomes Pareto dominates the desired payoff vector:
--
--   $$\operatorname{SurplusMax}\Longrightarrow\operatorname{CollusionProof}.$$
--
--   The result turns the statewise surplus comparison into the collusion condition used in Proposition 7.
--
--   **Formalization Note** The conclusion quantifies over all feasible state-dependent outcome lotteries. This is stronger than the paper's footnote 30, which quantifies only over other subgame-perfect equilibria.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 29 (PDF 30), §7, paragraph immediately following Proposition 7; footnote 30 on p. 28 (PDF 29)

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- §7, p. 29: if the desired outcome maximizes total agent surplus
state by state, no joint feasible outcome lottery Pareto improves upon it. -/
theorem surplus_implies_collusion_proof (P : Params) (hS : P.Standing)
    (C : Costs) (wA wB : ℝ)
    (hmax : SurplusMax P C .deleg wA wB) :
    CollusionProof P C .deleg wA wB := by sorry

end TeamDelegation.Optimal
