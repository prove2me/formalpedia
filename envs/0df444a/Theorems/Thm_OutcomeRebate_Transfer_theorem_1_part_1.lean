-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_theorem_1_part_1
-- name    : OutcomeRebate.Transfer.theorem_1_part_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:45.583754+00:00
-- url     : https://prove2.me/theorems/08a16c2e-4433-4186-b9ab-cde41b07f63a
-- title:
--   Theorem 1 part 1, p. 16 (PDF 17) — under uniform pricing the firm prices at p∗ and the payer covers
-- statement:
--   Under uniform pricing and Assumption 1, let $\bar q_1 \in (0,1)$ solve $zq = 1/\beta$. Suppose that $q \le \bar q_1$, or that $q > \bar q_1$ and
--   $$v' \ \ge\ p^*\Big(\frac1q - \frac{z\beta}{2}\Big) - \frac{\bar v}{2}, \qquad p^* = \frac c2 + \frac{\bar v}{2\beta z}.$$
--   Then $p^*$ is an equilibrium price, it is the only one, and the payer covers the drug at $p^*$.
--
--   This is the "unconstrained" region, where the payer's coverage decision does not bind and the firm prices at the optimum of its covered profit.
--
--   **Formalization Note** An equilibrium price is a $p \ge 0$ that maximizes the firm's profit over all $p' \ge 0$, each price evaluated at the payer's coverage response. "The firm prices at $p^*$" is read as: $p^*$ is the unique equilibrium price.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 16 (PDF 17), Theorem 1 part 1 (q̄1 defined below the theorem)

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Theorem 1 part 1 (p. 16). Under uniform pricing, with `q̄₁` the solution of `zq = 1/β` on
`(0, 1)`: if `q ≤ q̄₁`, or `q > q̄₁` and `v′ ≥ p∗(1/q − zβ/2) − v̄/2`, then the firm prices at `p∗`
(the unique equilibrium price) and the payer provides coverage. -/
theorem theorem_1_part_1 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (qbar1 : ℝ)
    (hqbar1 : 0 < qbar1 ∧ qbar1 < 1 ∧ zOf P.α P.lam qbar1 * qbar1 = 1 / P.β)
    (h : P.q ≤ qbar1 ∨
      (qbar1 < P.q ∧ pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2 ≤ P.vp)) :
    IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧
      ∀ p : ℝ, IsEqPriceU P p → p = pStar P := by sorry

end OutcomeRebate.Transfer
