-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_proposition_3_part_6
-- name    : OutcomeRebate.Transfer.proposition_3_part_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:12.589875+00:00
-- url     : https://prove2.me/theorems/e429a8ba-48a2-4db0-aaa4-448d6dcc73fc
-- title:
--   Proposition 3 part 6, p. 21 (PDF 22) — the payer's objective is higher under outcome-based pricing iff (q < q0, v′ > M′) or (q > q0, v′ < M′)
-- statement:
--   Suppose Assumptions 1 and 2 hold, and let $p^U$, $p^O$ be equilibrium prices. Then
--   $$W^O_{\text{payer}} - W^U_{\text{payer}} = \frac{n\beta c}{2\bar v}\,(qz - 1)\,(v' - M'),$$
--   with $M' = \frac{\bar v}{2}\big(\frac{\bar v}{z\beta^2c} - 1\big) + \frac{\beta c(2/\beta - 1 - zq)}{4q}$. The payer's objective is strictly higher under outcome-based pricing if and only if either
--   1. the drug is high-risk ($q < q_0$) and $v' > M'$, or
--   2. the drug is low-risk ($q > q_0$) and $v' < M'$.
--
--   Unless the payer's direct benefit is very high, the payer's and the firm's preferences between the two systems are opposed.
--
--   **Formalization Note** The closed-form difference is the display of the paper's proof (p. 56). The payer's side is its objective, payoff plus total patient payoff, at the equilibrium prices with the payer's coverage response.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 21 (PDF 22), Proposition 3 part 6; identity from its proof, p. 56 (PDF 57)

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Proposition 3 part 6 (p. 21), with the identity of its proof (p. 56). Under Assumption 2, at the
equilibrium prices: `W^O_payer − W^U_payer = (nβc/(2v̄))(qz − 1)(v′ − M′)`, and the payer's objective
is higher under outcome-based pricing iff either `q < q₀` and `v′ > M′`, or `q > q₀` and `v′ < M′`. -/
theorem proposition_3_part_6 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    realizedObjO P pO - realizedObjU P pU =
        P.n * P.β * P.c / (2 * P.vbar) * (P.q * P.z - 1) * (P.vp - Mprime P) ∧
      (realizedObjU P pU < realizedObjO P pO ↔
        (P.q < q0 P.α P.lam ∧ Mprime P < P.vp) ∨ (q0 P.α P.lam < P.q ∧ P.vp < Mprime P)) := by sorry

end OutcomeRebate.Transfer
