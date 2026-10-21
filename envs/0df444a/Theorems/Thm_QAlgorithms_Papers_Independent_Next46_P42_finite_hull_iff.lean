-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_finite_hull_iff
-- name    : QAlgorithms.Papers.Independent.Next46.P42.finite_hull_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:38:59.679702+00:00
-- url     : https://prove2.me/theorems/ee39e465-4e5f-4333-bb9f-d5e342fb5968
-- title:
--   §4, Lemma 2: finite hull versus measure roof
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For every channel and every state $\rho$,
--   $$
--   \widehat H_\Phi(\rho)=\operatorname{conv}H_\Phi(\rho)
--   \quad\Longleftrightarrow\quad
--   H_\Phi(\rho)<+\infty\ \text{or}\ \widehat H_\Phi(\rho)=+\infty.
--   $$
--   The finite convex hull uses finite decompositions into possibly mixed states. The equivalence follows the two cases explicitly established in the source proof and used by Proposition 5; the printed connective is “only if.” This characterizes when the finite and measure envelopes agree.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 9, §4, Lemma 2: finite hull versus measure roof

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

/-- PDF p.9, Lemma 2: the proof establishes the iff used in Proposition 5,
although the printed introductory connective is 'only if'. -/
theorem finite_hull_iff [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I) :
    (entropyRoof Phi.val rho.coefficients = finiteHull Phi.val rho.coefficients) ↔
      extendedEntropyNats (Phi.val rho.coefficients) < ⊤ ∨
        entropyRoof Phi.val rho.coefficients = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
