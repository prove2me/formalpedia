-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyhole_arc_integrand_bound
-- name    : WeightedRootIntegralIdentity.keyhole_arc_integrand_bound
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T10:39:55.506141+00:00
-- url     : https://prove2.me/theorems/b232cfdd-14d2-4a4a-ba2c-376d593e7dbb
-- title:
--   Norm bound for the keyhole integrand on a circular arc
-- statement:
--   If the numerator is bounded by M and a point on a circular arc has radius r>0, then the quotient integrand has norm at most M/r.
-- source:
--   The quotient norm identity and the defining radius equation of the circular arc.

import Mathlib

namespace WeightedRootIntegralIdentity

theorem keyhole_arc_integrand_bound {F : ℂ → ℂ} {z : ℂ} {M r : ℝ}
    (hF : ‖F z‖ ≤ M) (hr : 0 < r) (hz : ‖z‖ = r) :
    ‖F z / z‖ ≤ M / r := by sorry

end WeightedRootIntegralIdentity
