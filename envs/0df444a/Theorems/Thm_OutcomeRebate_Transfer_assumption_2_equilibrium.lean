-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_assumption_2_equilibrium
-- name    : OutcomeRebate.Transfer.assumption_2_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:13.325452+00:00
-- url     : https://prove2.me/theorems/03731326-4872-4669-a2df-7f6ff6607e32
-- title:
--   §4.1, p. 20 (PDF 21) — under Assumption 2, p^U = p∗, p^O = p̃∗ and the payer covers under both systems
-- statement:
--   Suppose Assumptions 1 and 2 hold, with $q_1 \in (0,1)$ the solution of $zq = 2/\beta$. Then:
--   1. under uniform pricing the unique equilibrium price is $p^U = p^*$, and the payer covers the drug there;
--   2. under outcome-based pricing the unique equilibrium price is $p^O = \tilde p^*$, and the payer covers the drug there.
--
--   This places the analysis of §4.1, Propositions 3 and 4, in the region where both systems price at their unconstrained optima with coverage.
--
--   **Formalization Note** Equilibrium prices are as in Theorems 1 and 2.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 20 (PDF 21), §4.1, Assumption 2 and the sentence following it

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- The consequence of Assumption 2 stated after it (p. 20): under uniform pricing the firm prices at
`p^U = p∗`, under outcome-based pricing at `p^O = p̃∗` (each the unique equilibrium price), and the
payer provides coverage under both systems. -/
theorem assumption_2_equilibrium (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1) :
    (IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧ ∀ p : ℝ, IsEqPriceU P p → p = pStar P) ∧
      (IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧
        ∀ p : ℝ, IsEqPriceO P p → p = pTilde P) := by sorry

end OutcomeRebate.Transfer
