-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_noisy_overlap_benchmark
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.noisy_overlap_benchmark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:17:14.497589+00:00
-- url     : https://prove2.me/theorems/9e79b4aa-1dd7-46bb-82ff-8c64b7921bcb
-- title:
--   Theorem 2 (Benchmark—mixed states), introduction (ii): exact noisy overlap
-- statement:
--   Let $s>0$ and $\eta\ge0$. Use the pure squeezed orbit $\rho_{s,\xi,\theta}$ of Theorem 1 and the additive-noise channel $N_\eta$ that adds $\eta I$ to the full-anticommutator covariance while preserving the mean. Thus each random displacement coordinate has variance $\eta/2$, and $N_0$ is the identity. For either all entanglement-breaking channels or all time-reversible channels $\mathcal T$,
--
--   $$\sup_{T\in\mathcal T}\inf_{\xi,\theta}\operatorname{Tr}[T(N_\eta(\rho_{s,\xi,\theta}))\rho_{s,\xi,\theta}]=\frac{1}{\sqrt{(1+\eta/2+1/s)(1+\eta/2+s)}}.$$
--
--   The heterodyne channel of Eq. (18) is admissible in both classes and attains the value at every displacement and phase. This is an overlap with the original pure target, not the Uhlmann fidelity of two mixed states.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 8, Theorem 2, Eq. (20)

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

/-- Theorem 2, pp.8–9, (20): exact noisy overlap with the ORIGINAL pure target;
the heterodyne strategy (18) attains it at every displacement and phase. -/
theorem noisy_overlap_benchmark (s eta : ℝ) (hs : 0 < s) (heta : 0 ≤ eta) :
    IsTraceClassChannel (additiveNoise eta) ∧
    (∀ reversible : Bool, flatBenchmark reversible s eta =
      1 / Real.sqrt ((1 + eta / 2 + 1 / s) * (1 + eta / 2 + s))) ∧
    (∀ reversible : Bool, benchmarkChannel reversible heterodyne) ∧
    (∀ (xi : ℝ × ℝ) (theta : ℝ), theta ∈ Set.Icc 0 (2 * Real.pi) →
      realFockTracePair (heterodyne (additiveNoise eta (squeezedOrbit s xi theta))) (squeezedOrbit s xi theta) =
        1 / Real.sqrt ((1 + eta / 2 + 1 / s) * (1 + eta / 2 + s))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
