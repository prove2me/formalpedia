-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_joint_surplus_identity
-- name    : OutcomeRebate.Transfer.joint_surplus_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:18.33668+00:00
-- url     : https://prove2.me/theorems/37ed265f-b05f-4af1-88bb-1de940fa7d19
-- title:
--   Proof of Proposition 4, p. 56 (PDF 57) — joint firm + payer gain = (nβc/(4v̄))(qz − 1)(2v′ + v̄ − 2c/q + βc/(2q) + βcz/2)
-- statement:
--   Under Assumption 1, evaluate the firm's profit and the payer's objective at $p^*$ (uniform) and $\tilde p^*$ (outcome-based), both with coverage ($\bar\beta = \beta$). Then
--   $$\Pi^O_{\text{firm}}(\tilde p^*;\beta) + W^O_{\text{payer}} - \big(\Pi^U_{\text{firm}}(p^*;\beta) + W^U_{\text{payer}}\big) = \frac{n\beta c}{4\bar v}\,(qz-1)\Big(2v' + \bar v - \frac{2c}{q} + \frac{\beta c}{2q} + \frac{\beta c z}{2}\Big).$$
--
--   This identity reduces the existence of a mutually beneficial transfer to a sign question.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 56 (PDF 57), proof of Proposition 4, first display

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- The joint-surplus identity of the proof of Proposition 4 (p. 56). At `p∗` and `p̃∗` with
coverage, `Π^O_firm(p̃∗; β) + W^O_payer − (Π^U_firm(p∗; β) + W^U_payer)
= (nβc/(4v̄))(qz − 1)(2v′ + v̄ − 2c/q + βc/(2q) + βcz/2)`. -/
theorem joint_surplus_identity (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) :
    firmProfitO P P.β (pTilde P) + payerObjO P P.β (pTilde P) -
        (firmProfitU P P.β (pStar P) + payerObjU P P.β (pStar P)) =
      P.n * P.β * P.c / (4 * P.vbar) * (P.q * P.z - 1) *
        (2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2) := by sorry

end OutcomeRebate.Transfer
