-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_optimal_measures_equivalence
-- name    : QAlgorithms.Papers.Independent.Next46.P42.optimal_measures_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:41:37.40689+00:00
-- url     : https://prove2.me/theorems/1f031b81-1ff6-412e-8636-6db19c7c4f7b
-- title:
--   §4, after Definition 2: equivalence of optimal measures
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   If $H_\Phi(\rho)<+\infty$, then for every generalized ensemble $\mu$,
--   $$
--   \mu\text{ is }\widehat H_\Phi\text{-optimal for }\rho
--   \quad\Longleftrightarrow\quad
--   \mu\text{ is }\chi_\Phi\text{-optimal for }\rho.
--   $$
--   Both optimality predicates require exact barycenter $\rho$ and pure-state support; the first attains the integrated entropy infimum and the second attains the integrated relative-entropy supremum. This identifies the two optimizer conventions on the finite-output-entropy domain.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 12, §4, after Definition 2: equivalence of optimal measures

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

/-- PDF p.12, after Definition 2: finite output entropy is essential. -/
theorem optimal_measures_equivalence [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I)
    (hfinite : extendedEntropyNats (Phi.val rho.coefficients) < ⊤) :
    ∀ mu : GeneralizedEnsemble I,
      RoofOptimal Phi.val rho.coefficients mu ↔ ChiOptimal Phi.val rho.coefficients mu := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
