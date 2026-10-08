-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyhole_bank_orientation
-- name    : WeightedRootIntegralIdentity.keyhole_bank_orientation
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T10:45:07.670769+00:00
-- url     : https://prove2.me/theorems/c87ace99-fcde-4604-8d60-952b3483bf9c
-- title:
--   Orientation reversal for the two slit banks
-- statement:
--   Reversing the orientation of an interval bank changes the sign of its complex line integral.
-- source:
--   The interval integral symmetry identity.

import Mathlib
open scoped Interval

namespace WeightedRootIntegralIdentity
open scoped Interval

theorem keyhole_bank_orientation {f : ℝ → ℂ} {a b : ℝ} :
    (∫ x in b..a, f x) = - ∫ x in a..b, f x := by sorry

end WeightedRootIntegralIdentity
