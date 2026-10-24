-- Prove2me | Theorems.Thm_PricingWithTips_served_buyer_alternatives_le
-- name    : PricingWithTips.served_buyer_alternatives_le
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:46:47.028982+00:00
-- url     : https://prove2.me/theorems/2c022de8-2999-4544-a456-98c3e36e30d3
-- title:
--   Adjusted matching bound for alternatives using already-served buyers
-- statement:
--   With courier–buyer separable costs and a welfare-optimal allocation, let courier utilities be maximal among feasible courier plans. Any alternative buyer–store matching that uses only buyers already served by the original allocation has adjusted weight no greater than the original matching. Other buyers may remain unmatched.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, pp. 20–23; alternating components not involving an unmatched buyer

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]

theorem served_buyer_alternatives_le [Nonempty B]
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → ∃ s₀ d₀, A.Trades b s₀ d₀) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
