-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_thermalEntropy_functionProperties
-- name    : QAlgorithms.Papers.Independent.Support50.P06.thermalEntropy_functionProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:32:37.396604+00:00
-- url     : https://prove2.me/theorems/f42ba50d-b21d-4347-8cb6-b3c123e1df75
-- title:
--   Thermal entropy and its inverse on the nonnegative ray
-- statement:
--   On $[0,\infty)$, let $g(N)=(N+1)\ln(N+1)-N\ln N$, with $0\ln0=0$. The function $g$ is nonnegative, nondecreasing and concave. Its inverse $g^{-1}$ on $[0,\infty)$ is nonnegative, nondecreasing and convex, and
--
--   $$g^{-1}(g(N))=N\quad(N\ge0),\qquad g(g^{-1}(S))=S\quad(S\ge0).$$
--
--   The accepted inverse is zero at zero and, for positive $S$, the infimum of $\{N\ge0:S\le g(N)\}$, a nonempty set bounded below. These properties justify entropy-matched thermal parameters, including the vacuum endpoint.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 3, §III, footnote 4: g and its inverse

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, footnote 4: nonnegativity, monotonicity, concavity of g and
nonnegativity, monotonicity, convexity of its genuine inverse, including both
inverse identities at zero. The inverse upper-level sets are nonempty and
bounded below on the positive domain; no empty real-infimum value is used. -/
theorem thermalEntropy_functionProperties :
    (∀ N : ℝ, 0 ≤ N → 0 ≤ g N) ∧
    MonotoneOn g (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) g ∧
    (∀ S : ℝ, 0 ≤ S → 0 ≤ thermalEntropyInverse S) ∧
    MonotoneOn thermalEntropyInverse (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) thermalEntropyInverse ∧
    (∀ N : ℝ, 0 ≤ N → thermalEntropyInverse (g N) = N) ∧
    (∀ S : ℝ, 0 ≤ S → g (thermalEntropyInverse S) = S) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
