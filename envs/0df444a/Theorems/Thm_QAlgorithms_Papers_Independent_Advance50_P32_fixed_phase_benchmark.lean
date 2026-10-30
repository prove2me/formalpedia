-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_fixed_phase_benchmark
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.fixed_phase_benchmark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:23:13.087996+00:00
-- url     : https://prove2.me/theorems/75f707f8-9867-4dd1-a14b-71d0d423da02
-- title:
--   Section 4.1, unnumbered fixed-phase benchmark
-- statement:
--   Fix a known squeezing $s>0$ and a known phase $\theta\in[0,2\pi]$. Optimize a channel independently of the unknown displacement $\xi\in\mathbb R^2$, with pure inputs $W_\xi U_\theta\rho_sU_\theta^*W_\xi^*$. For either all entanglement-breaking channels or all time-reversible channels $\mathcal T$,
--
--   $$\sup_{T\in\mathcal T}\inf_{\xi}\operatorname{Tr}[T(\rho_{s,\xi,\theta})\rho_{s,\xi,\theta}]=\frac12\ge\frac{\sqrt s}{1+s}.$$
--
--   The optimizing channel may depend on the known squeezing and phase. This is a distinct ensemble from the uniformly randomized phase ensemble and explains the effect of randomizing the phase. It does not assert optimality of the unsqueezed heterodyne channel at fixed phase.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 7, Section 4.1, fixed-phase paragraph

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

/-- Section 4.1, p.7: fixed known phase gives benchmark 1/2 for every s>0.
The optimizing channel may depend on the known phase and squeezing. -/
theorem fixed_phase_benchmark (s theta : ℝ) (hs : 0 < s)
    (htheta : theta ∈ Set.Icc 0 (2 * Real.pi)) :
    (∀ reversible : Bool, fixedPhaseBenchmark reversible s theta = 1 / 2) ∧
    Real.sqrt s / (1 + s) ≤ 1 / 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
