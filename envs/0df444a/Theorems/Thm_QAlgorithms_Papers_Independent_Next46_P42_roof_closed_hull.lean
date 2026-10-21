-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_roof_closed_hull
-- name    : QAlgorithms.Papers.Independent.Next46.P42.roof_closed_hull
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:43:26.294972+00:00
-- url     : https://prove2.me/theorems/86700ec7-94fa-49f5-b9c7-16771a05dba4
-- title:
--   §4, Proposition 5: integral roof equals convex closure
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Let $\overline{\operatorname{conv}}H_\Phi$ be the greatest closed convex minorant of output entropy, distinguished from the finite mixed-ensemble hull. Then globally
--   $$
--   \widehat H_\Phi=\overline{\operatorname{conv}}H_\Phi,
--   $$
--   and at every state $\rho$,
--   $$
--   \bigl[\overline{\operatorname{conv}}H_\Phi(\rho)=\operatorname{conv}H_\Phi(\rho)<+\infty\bigr]
--   \Longleftrightarrow H_\Phi(\rho)<+\infty.
--   $$
--   The finiteness condition is essential in the second formula. This identifies the measure roof with the closed convex envelope.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 13, §4, Proposition 5: integral roof equals convex closure

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

/-- PDF p.13, Proposition 5: global closed hull identity and finite-valued iff. -/
theorem roof_closed_hull [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) :
    (∀ rho : State I, entropyRoof Phi.val rho.coefficients = closedHull Phi.val rho.coefficients) ∧
    (∀ rho : State I,
      (closedHull Phi.val rho.coefficients = finiteHull Phi.val rho.coefficients ∧
        finiteHull Phi.val rho.coefficients < ⊤) ↔
        extendedEntropyNats (Phi.val rho.coefficients) < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
