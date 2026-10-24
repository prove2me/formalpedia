-- Prove2me | Theorems.Thm_PricingWithTips_sold_store_alternatives_le
-- name    : PricingWithTips.sold_store_alternatives_le
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:42:00.112453+00:00
-- url     : https://prove2.me/theorems/1c71f16e-df7a-4383-b2ce-1627820f337e
-- title:
--   Adjusted matching bound for alternatives using already-sold stores
-- statement:
--   With courier–store separable costs and a welfare-optimal allocation, let courier utilities be maximal among feasible courier plans. Any alternative buyer–store matching that uses only stores sold by the original allocation has adjusted weight no greater than the original matching. The allocation may leave other stores unsold.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, Appendix D, pp. 35–36; the alternating components not involving an unmatched store

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]

theorem sold_store_alternatives_le [Nonempty B]
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → A.Sells s) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
