-- Prove2me | Theorems.Thm_PricingWithTips_adjustedValue_buyer_off_order
-- name    : PricingWithTips.adjustedValue_buyer_off_order
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:18:18.470894+00:00
-- url     : https://prove2.me/theorems/e673c99c-9b12-4c2c-85cd-1b654dba5893
-- title:
--   Adjusted value under courier–buyer cost decomposition
-- statement:
--   Under structured courier costs, an undelivered order’s adjusted value equals its buyer valuation minus the buyer–store cost and an infimum surcharge that depends only on the buyer.
-- source:
--   Theorem 5.2 of arXiv:2507.10872; private mission proof support

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem adjustedValue_buyer_off_order [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - cBS b s - (⨅ d, cDB d b + uBar d) := by sorry

end PricingWithTips
