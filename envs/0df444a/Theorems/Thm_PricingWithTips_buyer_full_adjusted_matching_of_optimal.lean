-- Prove2me | Theorems.Thm_PricingWithTips_buyer_full_adjusted_matching_of_optimal
-- name    : PricingWithTips.buyer_full_adjusted_matching_of_optimal
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:36:08.209043+00:00
-- url     : https://prove2.me/theorems/cb217585-8ac6-4430-ad74-dcd4fc992b10
-- title:
--   Adjusted matching optimality when every buyer is served
-- statement:
--   Suppose a welfare-optimal allocation serves every buyer and delivery cost separates into buyer–store and courier–buyer terms. Under a maximal feasible courier-utility vector, its induced buyer–store matching maximizes total value net of required tips. This isolates the full-buyer subcase of the courier–buyer argument.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, pp. 20–23 (full-buyer subcase)

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem buyer_full_adjusted_matching_of_optimal [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ b, ∃ s d, A.Trades b s d)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
