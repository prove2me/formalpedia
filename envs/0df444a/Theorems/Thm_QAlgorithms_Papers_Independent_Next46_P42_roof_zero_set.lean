-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_roof_zero_set
-- name    : QAlgorithms.Papers.Independent.Next46.P42.roof_zero_set
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:45:24.649983+00:00
-- url     : https://prove2.me/theorems/a8bb88b6-fc24-43f3-8983-a55ba8085642
-- title:
--   §4, Proposition 6: zero set of the roof
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Let $Z$ be the set of normalized pure input states with zero output entropy. Then
--   $$
--   \{\rho:\widehat H_\Phi(\rho)=0\}
--   =\overline{\operatorname{conv}}^{\|\cdot\|_1} Z.
--   $$
--   The right-hand side is the trace-norm closure of the set’s finite convex hull. An empty generating set gives an empty zero set. This characterizes the exact zeros of the integral roof.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 16, §4, Proposition 6: zero set of the roof

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

/-- PDF p.16, Proposition 6: trace-norm closure of the convex hull of pure zero-output states. -/
theorem roof_zero_set [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) :
    {rho : State I | entropyRoof Phi.val rho.coefficients = 0} =
      {rho : State I | rho.coefficients ∈ traceClosure (convexHull ℝ
        {X : Matrix I I ℂ | ∃ psi : PureState I,
          X = psi.val.coefficients ∧ extendedEntropyNats (Phi.val X) = 0})} := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
