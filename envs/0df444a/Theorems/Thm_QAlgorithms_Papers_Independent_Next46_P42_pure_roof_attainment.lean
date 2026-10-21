-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_pure_roof_attainment
-- name    : QAlgorithms.Papers.Independent.Next46.P42.pure_roof_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:40:55.95913+00:00
-- url     : https://prove2.me/theorems/a6fe113a-3eca-43e0-a960-5491901eb912
-- title:
--   §4, Proposition 3: attained pure-state roof and finite-rank ensembles
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Every state $\rho$ has a Borel probability law $\mu$ with exact barycenter $\rho$, supported on normalized pure states, such that
--   $$
--   \widehat H_\Phi(\rho)=\int H_\Phi(\sigma)\,\mu(d\sigma).
--   $$
--   An optimal pure-supported law can have finite support if and only if $\rho$ has finite rank. If its rank is $n$, an optimal labelled pure ensemble with at most $n^2$ slots exists. Repeated or zero-probability slots may pad the ensemble. This is a bound on ensemble size, rather than an identification of rank from arbitrary distinct support cardinality. Attainment includes the value $+\infty$. This supplies optimizers for the integral roof.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 10, §4, Proposition 3: attained pure-state roof and finite-rank ensembles

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

/-- PDF pp.10–12, Proposition 3. Printed: support consisting of n^2 atoms iff
rank n. Changed: finite support iff finite rank, and at rank n an optimal law
has a pure ensemble of at most n^2 slots. The proof supplies exactly this bound;
arbitrary distinct optimal support cardinality does not determine rank. -/
theorem pure_roof_attainment [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I) :
    (∃ mu : GeneralizedEnsemble I, RoofOptimal Phi.val rho.coefficients mu) ∧
    ((∃ mu : GeneralizedEnsemble I, RoofOptimal Phi.val rho.coefficients mu ∧ HasFiniteSupport mu) ↔
      ∃ n, RankAtMost rho.coefficients n) ∧
    (∀ n, HasRank rho.coefficients n →
      ∃ (m : ℕ) (e : LabelledEnsemble I m) (mu : GeneralizedEnsemble I),
        m ≤ n^2 ∧ (∀ i, e.state i ∈ pureStates I) ∧ e.average = rho.coefficients ∧
        (mu : Measure (State I)) = e.law ∧ RoofOptimal Phi.val rho.coefficients mu) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
