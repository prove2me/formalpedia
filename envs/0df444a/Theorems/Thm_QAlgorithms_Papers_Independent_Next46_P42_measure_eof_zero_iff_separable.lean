-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_measure_eof_zero_iff_separable
-- name    : QAlgorithms.Papers.Independent.Next46.P42.measure_eof_zero_iff_separable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:52:24.907355+00:00
-- url     : https://prove2.me/theorems/722b65dc-8615-4397-a0ac-6928188452bb
-- title:
--   §7, zero EoF iff nonentangled
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For every normalized bipartite trace-class state,
--   $$
--   E_F^2(\rho)=0\quad\Longleftrightarrow\quad\rho\text{ is separable}.
--   $$
--   Separability means membership in the trace-norm closed convex hull of product pure states. It does not mean the existence of a countable product decomposition. This identifies the exact zero set of measure EoF.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 21, §7, zero EoF iff nonentangled

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

/-- PDF p.21: zero measure EoF iff trace-norm closed-convex-hull separability.
The accepted pureProductIntegral identifies this with closure of pure products. -/
theorem measure_eof_zero_iff_separable [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    (rho : State (I × K)) :
    measureEof rho.coefficients = 0 ↔ IsSeparable rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
