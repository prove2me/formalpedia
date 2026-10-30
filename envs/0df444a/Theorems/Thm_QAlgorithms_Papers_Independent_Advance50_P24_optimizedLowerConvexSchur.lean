-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_optimizedLowerConvexSchur
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.optimizedLowerConvexSchur
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:04:11.831331+00:00
-- url     : https://prove2.me/theorems/e435c8e6-24d1-4bc6-a85b-bea82de319ec
-- title:
--   Convexity, Schur-convexity and attainment of the optimized lower bound
-- statement:
--   Let $m\ge1$ and $N\ge0$. For $\eta\in[0,1]^m$, define
--
--   $$L^M(\eta,N)=\max_{a_i\ge0,\ \sum_i a_i=N}\sum_{i=1}^m L(\eta_i,a_i),$$
--
--   where $L$ is the piecewise scalar lower bound in nats, continuously interpreted at zero energy. This maximum is attained, and $L^M(\cdot,N)$ is convex and Schur-convex on $[0,1]^m$: if $y$ majorizes $x$, then $L^M(x,N)\le L^M(y,N)$.
--
--   This is full convexity, not just a midpoint inequality. Equations (50)–(53) supply the summation missing from printed (49).
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 5, Lemma 3, (49): convexity and Schur-convexity of the optimized lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)

open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3, PDF p.5, corrected (49)--(53): full convexity and Schur-convexity.
The printed objective lacks a sum; (50)--(53) uniquely supply it. The permutation
polytope definition majorizedBy x y means y majorizes x, with equal total sums. -/
theorem optimizedLowerConvexSchur {m : ℕ} (hm : 0 < m) (N : ℝ) (hN : 0 ≤ N) :
    ConvexOn ℝ (transmissivityCube m) (fun eta => parallelLower eta N) ∧
    (∀ x ∈ transmissivityCube m, ∀ y ∈ transmissivityCube m,
      majorizedBy x y → parallelLower x N ≤ parallelLower y N) ∧
    (∀ eta ∈ transmissivityCube m, ∃ a ∈ photonBudgetAllocations m N,
      parallelLower eta N = ∑ i, lowerBound (eta i) (a i)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
