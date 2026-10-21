-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_lift_labelled_ensembles
-- name    : QAlgorithms.Papers.Independent.Next46.P42.lift_labelled_ensembles
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:35:55.990274+00:00
-- url     : https://prove2.me/theorems/4b36f81c-1531-4407-9151-ae223fd5e052
-- title:
--   §3, Lemma 1: lifting convergent averages to labelled ensembles
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Let $(p_i,\rho_i)_{i=1}^m$ be a normalized labelled ensemble with average $\rho$, allowing zero probabilities. If $\rho_n\to\rho$ in trace norm, there are normalized ensembles $(p_i^{(n)},\rho_i^{(n)})_{i=1}^m$ with the same number of slots such that
--   $$
--   p_i^{(n)}\to p_i,\qquad \rho_i^{(n)}\to\rho_i,\qquad
--   \sum_{i=1}^m p_i^{(n)}\rho_i^{(n)}=\rho_n.
--   $$
--   Each component-state convergence is in trace norm. Normalization already excludes $m=0$. This gives perturbations of an ensemble with prescribed nearby average.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 6, §3, Lemma 1: lifting convergent averages to labelled ensembles

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

/-- PDF p.6, Lemma 1: the number of labelled slots is fixed; zero slots are impossible. -/
theorem lift_labelled_ensembles [Countable I] [Nonempty I]
    {m : ℕ} (e : LabelledEnsemble I m)
    (rho : State I) (he : e.average = rho.coefficients)
    (rhoSeq : ℕ → State I) (hseq : Tendsto rhoSeq atTop (nhds rho)) :
    ∃ es : ℕ → LabelledEnsemble I m,
      (∀ i, Tendsto (fun n => (es n).weight i) atTop (nhds (e.weight i))) ∧
      (∀ i, Tendsto (fun n => (es n).state i) atTop (nhds (e.state i))) ∧
      ∀ n, (es n).average = (rhoSeq n).coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
