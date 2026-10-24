-- Prove2me | Theorems.Thm_PricingWithTips_store_nonfull_adjusted_matching_of_maximal
-- name    : PricingWithTips.store_nonfull_adjusted_matching_of_maximal
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:32:14.157127+00:00
-- url     : https://prove2.me/theorems/cb02794b-af94-40ea-b8fd-03c6b40a73e0
-- title:
--   Adjusted matching optimality with unsold stores and courier–store costs
-- statement:
--   In a welfare-optimal market where delivery cost is a buyer–store term plus a courier–store term, at least one store is unsold and at least one courier is idle, but some trade occurs: the induced buyer matching maximizes value net of required tips computed from any maximal courier-utility vector.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2; Appendix D, pp. 35–36 (unsold-store case)

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem store_nonfull_adjusted_matching_of_maximal
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierStoreDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hstore : ¬ ∀ s, A.Sells s)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
