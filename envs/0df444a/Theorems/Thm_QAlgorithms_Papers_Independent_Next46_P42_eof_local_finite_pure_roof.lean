-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_eof_local_finite_pure_roof
-- name    : QAlgorithms.Papers.Independent.Next46.P42.eof_local_finite_pure_roof
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:55:24.300051+00:00
-- url     : https://prove2.me/theorems/61f46db4-0f81-403b-b6bd-dc77384db62e
-- title:
--   §7, local finite pure-ensemble formula for EoF
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For any bipartite state $\rho$ and real $\epsilon>0$, let $c_\epsilon(\rho)$ be the infimum of the average marginal entropy over all finite normalized pure-state ensembles whose average is within trace-norm distance $\epsilon$ of $\rho$. Then
--   $$
--   E_F^2(\rho)=\lim_{\epsilon\downarrow0}c_\epsilon(\rho).
--   $$
--   The average need not equal $\rho$ exactly. An empty feasible set has infimum $+\infty$, and the limiting value may be infinite. This is the local finite pure-ensemble representation.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 22, §7, local finite pure-ensemble formula for EoF

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

/-- PDF p.22, last display: local finite pure-ensemble formula as epsilon decreases
through positive reals; limits and empty feasible infima are extended nonnegative. -/
theorem eof_local_finite_pure_roof [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    (rho : State (I × K)) :
    Tendsto (localPureCost rho.coefficients) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (measureEof rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
