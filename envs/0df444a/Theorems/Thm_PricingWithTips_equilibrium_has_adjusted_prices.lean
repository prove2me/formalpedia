-- Prove2me | Theorems.Thm_PricingWithTips_equilibrium_has_adjusted_prices
-- name    : PricingWithTips.equilibrium_has_adjusted_prices
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:26:47.100415+00:00
-- url     : https://prove2.me/theorems/a1b45bb4-c6ca-431e-8223-6a6ec1b1f5cc
-- title:
--   Equilibrium yields prices for adjusted buyer values
-- statement:
--   Fix a delivery allocation and a maximal feasible courier-utility vector. If a with-tip equilibrium supports that allocation, then store prices can be chosen nonnegative so that every buyer maximizes adjusted value minus price, unmatched buyers prefer opting out, and every unsold store has price zero. The adjusted value subtracts the minimum tip implied by the maximal courier utilities. This is the courier-to-Walrasian translation in the only-if direction of Lemma 4.4.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Lemma 4.4 proof in Appendix C, pp. 33–34 and preceding Lemma 4.3.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem equilibrium_has_adjusted_prices [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar)
    (heq : HasWithTipEquilibriumAt M A) :
    ∃ p : S → ℝ,
      (∀ s, 0 ≤ p s) ∧
      (∀ b,
        match A.toBuyerMatching.assigned b with
        | none => ∀ s, adjustedValue M A uBar b s - p s ≤ 0
        | some s =>
            0 ≤ adjustedValue M A uBar b s - p s ∧
              ∀ s', adjustedValue M A uBar b s' - p s' ≤
                adjustedValue M A uBar b s - p s) ∧
      (∀ s, (¬ ∃ b, A.toBuyerMatching.assigned b = some s) → p s = 0) := by sorry

end PricingWithTips
