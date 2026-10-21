-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_measure_eof_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P42.measure_eof_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:51:48.016306+00:00
-- url     : https://prove2.me/theorems/632cd6d1-f5b3-4ca1-aa61-8a4ad0bd0855
-- title:
--   §7, measure-roof EoF: regularity, convex closure and pure attainment
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For a bipartite state, define $E_F^2$ as the integral roof of the output entropy of $\operatorname{Tr}_B$, over all state-space probability laws with exact barycenter. Then it is convex and trace-norm lower semicontinuous, and for every state $\rho$,
--   $$
--   E_F^2(\rho)=\overline{\operatorname{conv}}(H\circ\operatorname{Tr}_B)(\rho)
--   =\int H(\operatorname{Tr}_B\sigma)\,\mu(d\sigma)
--   $$
--   for some probability law $\mu$ with barycenter $\rho$ supported on normalized pure bipartite states. Infinite values are allowed. These are the global regularity and attainment properties of the measure EoF.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 21, §7, measure-roof EoF: regularity, convex closure and pure attainment

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter IsTraceClassChannel traceSize traceClosure
    productCoeff IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel IsPositive TraceOperatorLE RankAtMost SpectralPresentation spectralTruncation
    convexOperatorMixture traceSecond traceFirst channelTensorAction boundedConjugation)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage HasFiniteSupport pureStates extendedEntropyNats
    extendedRelativeEntropyNats relativeIntegral finiteEnsembleCapacity stateChi)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P42

variable {I J K L : Type}

/-- PDF p.21: measure EoF is convex, lower semicontinuous, the closed output-entropy
hull of the partial trace, and has a pure-state-supported minimizing law at every state. -/
theorem measure_eof_properties [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    :
    ConvexOnStates (@measureEof I K) ∧
    LowerSemicontinuous (fun rho : State (I × K) => measureEof rho.coefficients) ∧
    (∀ rho : State (I × K), measureEof rho.coefficients = closedHull (@traceSecond I K) rho.coefficients ∧
      ∃ mu : GeneralizedEnsemble (I × K), RoofOptimal (@traceSecond I K) rho.coefficients mu) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
