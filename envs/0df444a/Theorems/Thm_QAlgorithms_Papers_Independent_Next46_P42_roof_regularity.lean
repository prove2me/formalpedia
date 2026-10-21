-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_roof_regularity
-- name    : QAlgorithms.Papers.Independent.Next46.P42.roof_regularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:42:27.177489+00:00
-- url     : https://prove2.me/theorems/c9bae406-e93c-4adf-b320-062b3114ce14
-- title:
--   §4, Proposition 4: convexity, semicontinuity and closedness
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   The integral roof is convex and lower semicontinuous on the entire state space. Its real vertical epigraph is closed in trace norm times the ordinary real topology:
--   $$
--   \operatorname{epi}(\widehat H_\Phi)
--   =\{(\rho,r)\in\mathfrak S(\mathcal H)\times\mathbb R:\widehat H_\Phi(\rho)\le r\}
--   \quad\text{is closed}.
--   $$
--   Infinite values have empty vertical fibers. This states closedness in the source’s convex-analysis sense as well as lower semicontinuity.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 12, §4, Proposition 4: convexity, semicontinuity and closedness

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

/-- PDF pp.12–13, Proposition 4: convexity, lower semicontinuity and epigraph closedness. -/
theorem roof_regularity [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) :
    ConvexOnStates (entropyRoof Phi.val) ∧
    LowerSemicontinuous (fun rho : State I => entropyRoof Phi.val rho.coefficients) ∧
    IsClosed (realEpigraph (entropyRoof Phi.val)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
