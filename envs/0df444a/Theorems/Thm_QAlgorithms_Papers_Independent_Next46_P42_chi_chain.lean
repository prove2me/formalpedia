-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_chi_chain
-- name    : QAlgorithms.Papers.Independent.Next46.P42.chi_chain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:38:06.05863+00:00
-- url     : https://prove2.me/theorems/2a21696f-d939-47b2-9cd1-ece2315ede3d
-- title:
--   §3, Proposition 2: both chain inequalities
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For composable channels $\Phi,\Psi$ and every input state $\rho$,
--   $$
--   \chi_{\Psi\circ\Phi}(\rho)\le\chi_\Phi(\rho),\qquad
--   \chi_{\Psi\circ\Phi}(\rho)\le\chi_\Psi(\Phi(\rho)).
--   $$
--   Both bounds refer to the same initial input and hold with extended nonnegative values. They describe the two chain inequalities for the chi function.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 8, §3, Proposition 2: both chain inequalities

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

/-- PDF p.8, Proposition 2: both chain inequalities at the same input. -/
theorem chi_chain [Countable I] [Nonempty I] [Countable J] [Nonempty J] [Countable K] [Nonempty K]
    (Phi : Channel I J) (Psi : Channel J K) (rho : State I) :
    stateChi (Psi.val ∘ Phi.val) rho ≤ stateChi Phi.val rho ∧
    stateChi (Psi.val ∘ Phi.val) rho ≤ finiteEnsembleCapacity Psi.val {sigma : State J | sigma.coefficients = Phi.val rho.coefficients} := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
