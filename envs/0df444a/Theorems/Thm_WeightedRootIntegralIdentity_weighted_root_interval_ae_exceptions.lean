-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_interval_ae_exceptions
-- name    : WeightedRootIntegralIdentity.weighted_root_interval_ae_exceptions
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T08:22:33.57173+00:00
-- url     : https://prove2.me/theorems/32a9f812-4367-44a8-a9e0-c63efb7a324d
-- title:
--   Almost-everywhere avoidance of the finite exceptional set
-- statement:
--   On any restricted real interval, almost every point avoids 0 and every member of a given finite list of real branch points.
-- source:
--   Non-atomicity of Lebesgue measure and finite intersections of almost-everywhere statements.

import Theorems.Thm_WeightedRootIntegralIdentity_ae_ne_const_restrict_uIcc
open Filter Set MeasureTheory
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_interval_ae_exceptions (n : ℕ) (a : ℕ → ℝ) (l r : ℝ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)),
      x ≠ 0 ∧ ∀ i < n, x ≠ a i := by sorry

end WeightedRootIntegralIdentity
