-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_joint_surplus_bracket_pos
-- name    : OutcomeRebate.Transfer.joint_surplus_bracket_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:05.932383+00:00
-- url     : https://prove2.me/theorems/37339797-7ee2-48c1-abe4-d194c2a8ef71
-- title:
--   Proof of Proposition 4, pp. 56–57 (PDF 57–58) — under Assumptions 1–2, 2v′ + v̄ − 2c/q + βc/(2q) + βcz/2 > 0
-- statement:
--   Suppose Assumptions 1 and 2 hold, with $q_1 \in (0,1)$ the solution of $zq = 2/\beta$. Then
--   $$2v' + \bar v - \frac{2c}{q} + \frac{\beta c}{2q} + \frac{\beta c z}{2} \ >\ 0 .$$
--
--   By the joint-surplus identity, the joint gain of firm and payer from outcome-based pricing therefore has the sign of $qz - 1$. It is positive for high-risk drugs and negative for low-risk drugs.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), pp. 56–57 (PDF 57–58), proof of Proposition 4, the two displayed chains and the closing sentence

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- The bracket of the joint-surplus identity is positive (proof of Proposition 4, pp. 56–57):
under Assumptions 1 and 2, `2v′ + v̄ − 2c/q + βc/(2q) + βcz/2 > 0`, so the joint surplus change
has the sign of `qz − 1`. -/
theorem joint_surplus_bracket_pos (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1) :
    0 < 2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2 := by sorry

end OutcomeRebate.Transfer
