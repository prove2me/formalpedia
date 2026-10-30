-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_parallelCapacityBounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.parallelCapacityBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:01:16.351744+00:00
-- url     : https://prove2.me/theorems/f0f93af4-6ad1-433a-8b39-0200529913fa
-- title:
--   Separate optimized lower and upper parallel bounds
-- statement:
--   Let $m\ge1$, $\eta\in[0,1]^m$ and $N\ge0$, for the physical parallel vacuum-loss channel (25) under a total codebook-average photon budget. Define $L(\eta,x)=g(\eta x)-g((1-\eta)x)$ for $\eta>1/2$ and zero otherwise, and $U(\eta,x)=g((2\eta-1)x)$ on that branch and zero otherwise. Here $g$ is the thermal entropy in nats with $g(0)=0$. Write $L^M$ and $U^M$ for the respective maxima of $\sum_i L(\eta_i,a_i)$ and $\sum_i U(\eta_i,a_i)$ over nonnegative allocations summing to $N$. Both maxima are attained, and
--
--   $$L^M(\eta,N)\le C_P^M(\eta,N)\le U^M(\eta,N).$$
--
--   The two optimizations have separate maximizing allocations. No large-transmissivity or equal-mode assumption is imposed.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 4, §IV-C, unnumbered: extension of both bounds to multiple modes

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

/-- PDF p.4, the unnumbered extension following (42): separately optimized
upper and lower bounds. Each real supremum is explicitly attained; its
maximizing allocation need not maximize the other bound. -/
theorem parallelCapacityBounds {m : ℕ} (hm : 0 < m) (eta : Fin m → ℝ)
    (heta : eta ∈ transmissivityCube m) (N : ℝ) (hN : 0 ≤ N) :
    ENNReal.ofReal (parallelLower eta N) ≤ parallelPrivateCapacityNats eta N ∧
    parallelPrivateCapacityNats eta N ≤ ENNReal.ofReal (parallelUpper eta N) ∧
    (∃ a ∈ photonBudgetAllocations m N, parallelLower eta N = ∑ i, lowerBound (eta i) (a i)) ∧
    (∃ b ∈ photonBudgetAllocations m N, parallelUpper eta N = ∑ i, upperBound (eta i) (b i)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
