-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_lowerBoundConvex
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.lowerBoundConvex
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:03:24.05778+00:00
-- url     : https://prove2.me/theorems/bbcd2674-2653-4000-ace0-e929ef287993
-- title:
--   Convexity of the single-mode lower bound
-- statement:
--   For every $N>0$, define $L(\eta,N)=g(\eta N)-g((1-\eta)N)$ for $\eta>1/2$ and zero otherwise, where $g(x)=(1+x)\log(1+x)-x\log x$ in nats and $g(0)=0$. Then
--
--   $$\eta\longmapsto L(\eta,N)\quad\text{is convex on }[0,1].$$
--
--   This includes both the zero branch and the endpoint $\eta=1$. It is a scalar analytic statement, with no capacity or derivative hypothesis.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 5, Lemma 2: convexity of the single-mode lower bound

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

/-- Lemma 2, PDF p.5: full convexity, including eta=1 and the zero branch.
The printed positive photon budget is retained; no derivative condition is assumed. -/
theorem lowerBoundConvex (N : ℝ) (hN : 0 < N) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun eta => lowerBound eta N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
