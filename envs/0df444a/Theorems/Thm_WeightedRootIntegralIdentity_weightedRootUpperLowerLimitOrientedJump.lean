-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootUpperLowerLimitOrientedJump
-- name    : WeightedRootIntegralIdentity.weightedRootUpperLowerLimitOrientedJump
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T06:19:25.164974+00:00
-- url     : https://prove2.me/theorems/5ce5ba82-383a-4369-b46a-ba145087a3eb
-- title:
--   Upper and lower bank limits give the oriented real-axis jump
-- statement:
--   If the upper bank integrals converge to A and the oppositely oriented lower bank integrals converge to the negative conjugate of A, then their sum converges to A minus its conjugate. This is the orientation-correct real-axis jump passage supplied by the upper/lower DCT and conjugacy lemmas.
-- source:
--   Combine the accepted upper-bank DCT identification, lower-bank conjugacy, and orientation reversal by continuity of addition.

import Mathlib
open Filter Topology
namespace WeightedRootIntegralIdentity
theorem weightedRootUpperLowerLimitOrientedJump
    (U L : ℕ → ℂ) (A : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A))) :
    Tendsto (fun m : ℕ => U m + L m) atTop
      (𝓝 (A - starRingEnd ℂ A)) := by sorry
end WeightedRootIntegralIdentity
