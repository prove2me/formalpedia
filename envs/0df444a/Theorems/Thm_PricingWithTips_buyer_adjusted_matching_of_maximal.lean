-- Prove2me | Theorems.Thm_PricingWithTips_buyer_adjusted_matching_of_maximal
-- name    : PricingWithTips.buyer_adjusted_matching_of_maximal
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:32:21.719783+00:00
-- url     : https://prove2.me/theorems/68e65594-4c56-4d1d-aa42-a80271ad13de
-- title:
--   Adjusted matching optimality under courier–buyer costs
-- statement:
--   In a welfare-optimal nonempty market with an idle courier, if delivery cost is a buyer–store term plus a courier–buyer term, then the induced buyer matching maximizes value net of required tips computed from any maximal courier-utility vector.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, pp. 20–23 (courier–buyer case)

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem buyer_adjusted_matching_of_maximal
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
