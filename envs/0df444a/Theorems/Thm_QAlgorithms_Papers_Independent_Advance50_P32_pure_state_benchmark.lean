-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_pure_state_benchmark
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.pure_state_benchmark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:16:02.415746+00:00
-- url     : https://prove2.me/theorems/f8180818-0ab1-4183-a570-18f8a93b5497
-- title:
--   Theorem 1 (Benchmark—pure states), abstract and introduction (i)
-- statement:
--   Let $s>0$ be the known squeezing, and let $\rho_{s,\xi,\theta}=W_\xi U_\theta\rho_sU_\theta^*W_\xi^*$, where $\rho_s$ is the centered pure one-mode Gaussian state with covariance $\operatorname{diag}(s,1/s)$, $\xi\in\mathbb R^2$, and $0\le\theta\le2\pi$. Covariance uses the full anticommutator and vacuum covariance $I$. For either all entanglement-breaking channels or all channels remaining completely positive after linear matrix transposition, denoted $\mathcal T$, the channel is chosen independently of the unknown displacement and phase, and
--
--   $$\sup_{T\in\mathcal T}\inf_{\xi,\theta}\operatorname{Tr}[T(\rho_{s,\xi,\theta})\rho_{s,\xi,\theta}]=\frac{\sqrt{s}}{1+s}.$$
--
--   The same heterodyne measure-and-prepare channel $H$, with effects $W_\zeta|0\rangle\langle0|W_\zeta^*/(2\pi)$ and preparation $W_\zeta|0\rangle$, belongs to both classes and attains this overlap at every input. These inputs are normalized density operators. This is the operational meaning of the formal flat-prior benchmark; there is no uniform probability measure on all of phase space.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 6, Theorem 1, Eqs. (11), (18), (19)

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

/-- Theorem 1, pp.5–7, (11),(18),(19): exact worst-case benchmark in both classes,
attained at every input by the same heterodyne channel. The formal flat average
is interpreted by its covariant worst-case value, never by Lebesgue probability. -/
theorem pure_state_benchmark (s : ℝ) (hs : 0 < s) :
    (∀ reversible : Bool, flatBenchmark reversible s 0 = Real.sqrt s / (1 + s)) ∧
    (∀ reversible : Bool, benchmarkChannel reversible heterodyne) ∧
    (∀ (xi : ℝ × ℝ) (theta : ℝ), theta ∈ Set.Icc 0 (2 * Real.pi) →
      IsDensity (squeezedOrbit s xi theta) ∧
      realFockTracePair (heterodyne (squeezedOrbit s xi theta)) (squeezedOrbit s xi theta) =
        Real.sqrt s / (1 + s)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
