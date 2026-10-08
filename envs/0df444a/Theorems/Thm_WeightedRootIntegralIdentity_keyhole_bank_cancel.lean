-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyhole_bank_cancel
-- name    : WeightedRootIntegralIdentity.keyhole_bank_cancel
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T10:47:18.47172+00:00
-- url     : https://prove2.me/theorems/cb9311ef-850a-4da3-a3b2-54e6c1dcee9e
-- title:
--   Cancellation of oppositely oriented bank integrals
-- statement:
--   Two identical interval integrands traversed in opposite orientations have integrals summing to zero.
-- source:
--   Interval-integral orientation reversal and ring arithmetic.

import Mathlib
open scoped Interval

namespace WeightedRootIntegralIdentity
open scoped Interval

theorem keyhole_bank_cancel {f : ℝ → ℂ} {a b : ℝ} :
    (∫ x in a..b, f x) + (∫ x in b..a, f x) = 0 := by sorry

end WeightedRootIntegralIdentity
