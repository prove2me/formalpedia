-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_eof_finite_marginals
-- name    : QAlgorithms.Papers.Independent.Next46.P42.eof_finite_marginals
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:53:51.32567+00:00
-- url     : https://prove2.me/theorems/1120fb5c-405d-43cc-a357-f7ddee61ac52
-- title:
--   §7, equation (22): EoF roofs coincide on finite-marginal-entropy states
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Let $E_F^1$ be the countable normalized pure-state roof with exact trace-norm barycenter, and $E_F^2$ the full probability-measure roof. If both marginals of a bipartite state have finite entropy, then
--   $$
--   H(\operatorname{Tr}_B\rho)<+\infty,\quad H(\operatorname{Tr}_A\rho)<+\infty
--   \quad\Longrightarrow\quad E_F^1(\rho)=E_F^2(\rho).
--   $$
--   This supplies the requested correspondence on precisely the finite-marginal-entropy domain. It does not identify the global tensor-additivity predicates for the two conventions.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 22, §7, equation (22): EoF roofs coincide on finite-marginal-entropy states

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

/-- PDF p.22, (22): both marginal entropies finite, without a Gaussian restriction. -/
theorem eof_finite_marginals [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    (rho : State (I × K))
    (hleft : extendedEntropyNats (traceSecond rho.coefficients) < ⊤)
    (hright : extendedEntropyNats (traceFirst rho.coefficients) < ⊤) :
    countableEof rho.coefficients = measureEof rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
