-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_cpow_norm_real_exponent
-- name    : WeightedRootIntegralIdentity.cpow_norm_real_exponent
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T08:27:00.137596+00:00
-- url     : https://prove2.me/theorems/226b04e2-ba94-444a-971b-be1e46978842
-- title:
--   Norm formula for a real-exponent complex power
-- statement:
--   For a complex base and a real exponent, the norm of the principal complex power equals the real power of the base norm. Applied to an upper offset of a real base, this removes the branch phase and is the starting point for uniform domination estimates.
-- source:
--   Standard norm identity for principal complex powers.

import Mathlib

namespace WeightedRootIntegralIdentity

theorem cpow_norm_real_exponent (b w ε : ℝ) :
    ‖((b : ℂ) + ε * Complex.I) ^ (w : ℂ)‖ =
      ‖(b : ℂ) + ε * Complex.I‖ ^ w := by sorry

end WeightedRootIntegralIdentity
