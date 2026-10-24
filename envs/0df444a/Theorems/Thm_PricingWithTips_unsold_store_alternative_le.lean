-- Prove2me | Theorems.Thm_PricingWithTips_unsold_store_alternative_le
-- name    : PricingWithTips.unsold_store_alternative_le
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:42:22.459999+00:00
-- url     : https://prove2.me/theorems/f00ae0fd-a157-49ca-9dd9-41cc385bf9f5
-- title:
--   Adjusted matching bound when an alternative introduces an unsold store
-- statement:
--   With courier–store separable costs, a welfare-optimal nonempty allocation and an idle courier, consider any alternative buyer matching that uses at least one store unsold by the original allocation. Its value net of required tips is no greater than that of the original buyer matching, for the maximal courier-utility vector.
-- source:
--   https://arxiv.org/abs/2507.10872, Theorem 5.2, Appendix D, pp. 35–36; alternating path ending at an unmatched store

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem unsold_store_alternative_le
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierStoreDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hnew : ∃ b s, z.assigned b = some s ∧ ¬ A.Sells s) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
