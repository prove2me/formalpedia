-- Prove2me | Theorems.Thm_PricingWithTips_store_full_adjusted_matching_of_optimal
-- name    : PricingWithTips.store_full_adjusted_matching_of_optimal
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:30:50.860917+00:00
-- url     : https://prove2.me/theorems/9deab4d8-981f-4bf3-a399-49c8db7c711b
-- title:
--   Adjusted matching optimality when all stores are sold
-- statement:
--   Suppose a welfare-optimal allocation sells every store and delivery cost separates into a buyer–store term plus a courier–store term. For any maximal feasible vector of courier utilities, the allocation’s buyer–store matching maximizes total value net of the required tips. This is the full-store subcase of the structured-cost argument.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, p. 20; Appendix D, pp. 35–36 (full-store subcase)

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem store_full_adjusted_matching_of_optimal [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ s, A.Sells s)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
