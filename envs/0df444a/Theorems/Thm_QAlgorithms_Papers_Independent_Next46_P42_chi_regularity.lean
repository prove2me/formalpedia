-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_chi_regularity
-- name    : QAlgorithms.Papers.Independent.Next46.P42.chi_regularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:35:07.244552+00:00
-- url     : https://prove2.me/theorems/c95960f1-ed6c-4298-8fb1-da0691f7a288
-- title:
--   §3, Proposition 1: global χ regularity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For every channel $\Phi$, the entire extended-valued function $\chi_\Phi$ is nonnegative and trace-norm lower semicontinuous. For all states $\rho,\sigma$ and $t\in[0,1]$,
--   $$
--   \chi_\Phi(t\rho+(1-t)\sigma)\ge t\chi_\Phi(\rho)+(1-t)\chi_\Phi(\sigma)\ge0.
--   $$
--   This is global regularity, including infinite values.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 5, §3, Proposition 1: global χ regularity

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

/-- PDF pp.5–7, Proposition 1: nonnegativity, global concavity and trace-norm lower semicontinuity. -/
theorem chi_regularity [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) :
    (∀ rho : State I, 0 ≤ stateChi Phi.val rho) ∧
    ConcaveOnStates (fun X => finiteEnsembleCapacity Phi.val {rho : State I | rho.coefficients = X}) ∧
    LowerSemicontinuous (fun rho : State I => stateChi Phi.val rho) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
