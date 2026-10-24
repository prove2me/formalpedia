-- Prove2me | Theorems.Thm_PricingWithTips_structured_costs_adjusted_matching_of_maximal
-- name    : PricingWithTips.structured_costs_adjusted_matching_of_maximal
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:11:41.801979+00:00
-- url     : https://prove2.me/theorems/c417e664-b4a6-4bcb-80de-b62cad6faa86
-- title:
--   Structured costs make the adjusted matching optimal
-- statement:
--   Let a welfare-optimal allocation have at least one delivered order and one idle courier. Suppose courier costs decompose into a buyer–store term plus either a courier–store term or a courier–buyer term. For its componentwise maximal courier utility profile, the induced buyer–store matching maximizes total adjusted value among all buyer–store matchings.
-- source:
--   Theorem 5.2 of arXiv:2507.10872; private mission final matching argument

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem structured_costs_adjusted_matching_of_maximal
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
