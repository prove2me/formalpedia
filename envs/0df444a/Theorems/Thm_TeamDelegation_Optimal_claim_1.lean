-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_claim_1
-- name    : TeamDelegation.Optimal.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:31.804893+00:00
-- url     : https://prove2.me/theorems/45726b09-3338-484e-8cc9-88efe8a268e6
-- title:
--   Claim 1: three inequalities imply all eight surplus constraints
-- statement:
--   Let $\Delta_{\mathrm{sum}}\ge0$ and $W=w_A+w_B$. Under Assumption 1, if constraints (60), (64), and (66) hold,
--
--   $$(p_2-p_0)W\ge2e,\qquad(p_2-q_2)W\ge\Delta_{\mathrm{sum}},\qquad(p_2-q_0)W\ge2e+\Delta_{\mathrm{sum}},$$
--
--   then every one of the eight surplus constraints (59)–(66) holds.
--
--   This reduces the surplus test used in Proposition 7 to three scalar inequalities.
--
--   **Formalization Note** $W$ is represented as a real argument; in the application it is the sum of the two delegated bonuses.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 38 (PDF 39), Claim 1

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Claim 1, p. 38: at a nonnegative sum of adoption-cost differences,
(60), (64), and (66) imply all eight surplus inequalities. -/
theorem claim_1 (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (W Δsum : ℝ) (hsum : 0 ≤ Δsum)
    (h60 : (P.p2 - P.p0) * W ≥ 2 * P.e)
    (h64 : (P.p2 - P.q2) * W ≥ Δsum)
    (h66 : (P.p2 - P.q0) * W ≥ 2 * P.e + Δsum) :
    SurplusConstraints P W Δsum := by sorry

end TeamDelegation.Optimal
