-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_eof_pure_and_separable
-- name    : QAlgorithms.Papers.Independent.Next46.P42.eof_pure_and_separable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:54:35.444987+00:00
-- url     : https://prove2.me/theorems/94570aec-a84f-423f-9edf-22d5c824694c
-- title:
--   §7, equality for pure and nonentangled states
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For the countable pure-state roof $E_F^1$ and measure roof $E_F^2$, every separable state satisfies $E_F^1(\rho)=E_F^2(\rho)=0$. Every normalized pure bipartite state $\psi$ satisfies
--   $$
--   E_F^1(\psi)=E_F^2(\psi)=H(\operatorname{Tr}_B\psi).
--   $$
--   No finite marginal entropy is required, and the pure-state values may be infinite. Separability is the closed convex hull convention, including countably nondecomposable states. This retains the separate assertion on page 22 for independent review.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 22, §7, equality for pure and nonentangled states

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

/-- PDF p.22: the separately asserted pure/separable equality, allowing infinite
marginal entropy. Separability is never replaced by countable product decomposability. -/
theorem eof_pure_and_separable [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    :
    (∀ rho : State (I × K), IsSeparable rho.coefficients →
      countableEof rho.coefficients = measureEof rho.coefficients ∧
      measureEof rho.coefficients = 0) ∧
    (∀ psi : PureState (I × K),
      countableEof psi.val.coefficients = measureEof psi.val.coefficients ∧
      measureEof psi.val.coefficients = extendedEntropyNats (traceSecond psi.val.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
