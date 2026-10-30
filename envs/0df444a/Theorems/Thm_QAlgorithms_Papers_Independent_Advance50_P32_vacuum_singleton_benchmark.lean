-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_vacuum_singleton_benchmark
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.vacuum_singleton_benchmark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:28:36.99528+00:00
-- url     : https://prove2.me/theorems/837cab1f-95bd-466e-adc8-b9d773fc28ab
-- title:
--   Section 5.3, unnumbered no-displacement vacuum special case
-- statement:
--   Take $s=1$, identity noise ($\lambda=1$), zero displacement with probability law $\delta_0$, and uniform phase rotations. Every state in the ensemble is the vacuum $|0\rangle\langle0|$. Therefore the entanglement-breaking benchmark is
--
--   $$\bar F=1.$$
--
--   The channel that discards its input and prepares the vacuum attains this value. The formal statement also records that all rotated ensemble states equal the vacuum. The displacement law is a point mass, not a Lebesgue density, so this boundary case does not apply a probability-density hypothesis to a delta function.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 15, Section 5.3, Figure 4 and final paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology TensorProduct

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State IsTraceClassChannel BreaksTraceClassEntanglement
   productCoeff traceSize rotationMeasure)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel vacuum realFockTracePair)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section 5.3, p.15 and Figure 4: s=1, no displacement, lambda=1.
The uniformly rotated ensemble is a singleton, with EB benchmark one attained
by vacuum preparation. The displacement law is Dirac mass, not a density. -/
theorem vacuum_singleton_benchmark :
    measureBenchmark 1 (Measure.dirac (0 : ℝ × ℝ)) = 1 ∧
    benchmarkChannel false vacuumReplacement ∧
    measureScore 1 (Measure.dirac (0 : ℝ × ℝ)) vacuumReplacement = 1 ∧
    (∀ theta : ℝ, priorOrbit 1 0 theta = vacuum 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
