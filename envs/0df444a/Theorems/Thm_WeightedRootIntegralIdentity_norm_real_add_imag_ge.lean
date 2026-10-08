-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_norm_real_add_imag_ge
-- name    : WeightedRootIntegralIdentity.norm_real_add_imag_ge
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T08:40:59.501086+00:00
-- url     : https://prove2.me/theorems/cffedb02-ece0-4f4c-a8d5-e034f783f656
-- title:
--   Real part lower-bounds the affine complex norm
-- statement:
--   For nonnegative real x and any real ε, the complex norm of x + ε i is at least x.
-- source:
--   The real part of a complex number is bounded above by its norm.

import Mathlib

namespace WeightedRootIntegralIdentity

theorem norm_real_add_imag_ge (x ε : ℝ) (hx : 0 ≤ x) :
    x ≤ ‖(x : ℂ) + ε * Complex.I‖ := by sorry

end WeightedRootIntegralIdentity
