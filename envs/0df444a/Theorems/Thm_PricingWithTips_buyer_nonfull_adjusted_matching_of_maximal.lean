-- Prove2me | Theorems.Thm_PricingWithTips_buyer_nonfull_adjusted_matching_of_maximal
-- name    : PricingWithTips.buyer_nonfull_adjusted_matching_of_maximal
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:37:09.848279+00:00
-- url     : https://prove2.me/theorems/7458c55a-0f36-45ac-8659-79d29c9d03b1
-- title:
--   Adjusted matching optimality with unmatched buyers and courier–buyer costs
-- statement:
--   In a welfare-optimal nonempty market with an idle courier and at least one unmatched buyer, if delivery cost separates into buyer–store and courier–buyer terms, then the induced buyer matching maximizes value net of required tips for any maximal courier-utility vector.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, pp. 20–23 (unmatched-buyer path case)

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem buyer_nonfull_adjusted_matching_of_maximal
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hbuyer : ¬ ∀ b, ∃ s d, A.Trades b s d)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
