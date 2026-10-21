-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_identity_roof_example
-- name    : QAlgorithms.Papers.Independent.Next46.P42.identity_roof_example
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:39:58.069577+00:00
-- url     : https://prove2.me/theorems/8430c81d-6adc-4080-9588-0da469c44d2e
-- title:
--   §4, noiseless-channel example: roof and finite hull differ
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For the identity channel, the measure roof vanishes at every state, while the finite hull is infinite at every infinite-entropy state:
--   $$
--   \widehat H_{\mathrm{id}}(\rho)=0,\qquad
--   H(\rho)=+\infty\Longrightarrow\operatorname{conv}H(\rho)=+\infty.
--   $$
--   If the system is infinite dimensional, such states exist, so a strict roof gap occurs and the finite hull is not trace-norm lower semicontinuous. The separately cited first-category assertion is background rather than part of this item. This example motivates use of the closed convex envelope.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 9, §4, noiseless-channel example: roof and finite hull differ

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

/-- PDF pp.9–10: identity-channel roof zero everywhere, with infinite-entropy
states exhibiting a strict gap in every infinite-dimensional system. -/
theorem identity_roof_example [Countable I] [Nonempty I]
    :
    (∀ rho : State I, entropyRoof id rho.coefficients = 0) ∧
    (∀ rho : State I, extendedEntropyNats rho.coefficients = ⊤ →
      finiteHull id rho.coefficients = ⊤) ∧
    (Infinite I →
      (∃ rho : State I, extendedEntropyNats rho.coefficients = ⊤ ∧
        entropyRoof id rho.coefficients < finiteHull id rho.coefficients) ∧
      ¬ LowerSemicontinuous (fun rho : State I => finiteHull id rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
