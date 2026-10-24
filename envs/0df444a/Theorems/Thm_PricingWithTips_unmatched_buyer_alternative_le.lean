-- Prove2me | Theorems.Thm_PricingWithTips_unmatched_buyer_alternative_le
-- name    : PricingWithTips.unmatched_buyer_alternative_le
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:47:06.680667+00:00
-- url     : https://prove2.me/theorems/73137924-045a-4c67-936d-dad7a42ba4ce
-- title:
--   Adjusted matching bound when an alternative introduces an unmatched buyer
-- statement:
--   With courier–buyer separable costs, a welfare-optimal nonempty allocation and an idle courier, consider an alternative buyer matching that serves at least one buyer who was originally unmatched. Its adjusted weight is no greater than the original buyer matching’s adjusted weight, for the maximal courier-utility vector.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, pp. 21–23; alternating path starting at an unmatched buyer

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem unmatched_buyer_alternative_le
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hnew : ∃ b s, z.assigned b = some s ∧ A.assigned b = none) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
