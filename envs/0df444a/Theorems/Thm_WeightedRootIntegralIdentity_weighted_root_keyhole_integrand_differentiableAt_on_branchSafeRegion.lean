-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_keyhole_integrand_differentiableAt_on_branchSafeRegion
-- name    : WeightedRootIntegralIdentity.weighted_root_keyhole_integrand_differentiableAt_on_branchSafeRegion
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-18T22:23:25.173863+00:00
-- url     : https://prove2.me/theorems/04a11e6a-d1f4-4e2b-b19b-ef6e97482d67
-- title:
--   Holomorphicity on the branch-safe weighted-root annulus
-- statement:
--   On the branch-safe annular domain, the weighted-root quotient is complex differentiable at every point.
-- source:
--   Factorwise principal-power differentiability on the slit plane and nonvanishing of the reciprocal denominator on the positive-radius annulus.

import Mathlib
import Definitions.Def_weightedRootBranchSafeRegion
import Definitions.Def_weightedRootKeyholeIntegrand
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_differentiableAt_of_shift_mem_slitPlane
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_keyhole_integrand_differentiableAt_on_branchSafeRegion
    (n : ℕ) (a w : ℕ → ℝ) (r R : ℝ) (z : ℂ)
    (hr : 0 < r) (hz : z ∈ weightedRootBranchSafeRegion n a r R) :
    DifferentiableAt ℂ (weightedRootKeyholeIntegrand n a w) z := by sorry

end WeightedRootIntegralIdentity
