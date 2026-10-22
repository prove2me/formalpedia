-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_theorem_2_part_1
-- name    : OutcomeRebate.Transfer.theorem_2_part_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:25.303837+00:00
-- url     : https://prove2.me/theorems/08dc9523-b0c7-4ff9-9b36-f758506ec018
-- title:
--   Theorem 2 part 1, p. 19 (PDF 20) — under outcome-based pricing the firm prices at p̃∗ and the payer covers
-- statement:
--   Under outcome-based pricing and Assumption 1, suppose
--   $$v' \ \ge\ \tilde p^*\Big(1 - \frac\beta2\Big) - \frac{\bar v}{2}, \qquad \tilde p^* = \frac{c}{2q} + \frac{\bar v}{2\beta}.$$
--   Then $\tilde p^*$ is an equilibrium price, it is the only one, and the payer covers the drug at $\tilde p^*$.
--
--   This is the outcome-based counterpart of Theorem 1 part 1.
--
--   **Formalization Note** Equilibrium prices are defined as for Theorem 1. "The firm prices at $\tilde p^*$" is read as uniqueness of the equilibrium price.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 19 (PDF 20), Theorem 2 part 1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Theorem 2 part 1 (p. 19). Under outcome-based pricing, if `v′ ≥ p̃∗(1 − β/2) − v̄/2`, the firm
prices at `p̃∗` (the unique equilibrium price) and the payer provides coverage. -/
theorem theorem_2_part_1 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (h : pTilde P * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp) :
    IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧
      ∀ p : ℝ, IsEqPriceO P p → p = pTilde P := by sorry

end OutcomeRebate.Transfer
