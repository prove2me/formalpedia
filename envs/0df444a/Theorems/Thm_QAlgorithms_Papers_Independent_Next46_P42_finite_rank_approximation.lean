-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_finite_rank_approximation
-- name    : QAlgorithms.Papers.Independent.Next46.P42.finite_rank_approximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:44:11.60847+00:00
-- url     : https://prove2.me/theorems/d446aeda-cc01-4af9-988d-0f0497aee96d
-- title:
--   §4, Lemma 3: finite-rank finite-output-entropy approximation
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   If $\widehat H_\Phi(\rho)<+\infty$, there is a sequence of finite-rank states $\rho_n$ with finite output entropy at every index such that
--   $$
--   \rho_n\to\rho\text{ in trace norm},\qquad
--   H_\Phi(\rho_n)<+\infty,\qquad
--   \widehat H_\Phi(\rho_n)\to\widehat H_\Phi(\rho).
--   $$
--   No finite output entropy is required at the limiting state. This approximation preserves the roof value while giving finite output entropy and finite rank.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 14, §4, Lemma 3: finite-rank finite-output-entropy approximation

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

/-- PDF pp.14–15, Lemma 3: finite roof at the target; finite output entropy is a conclusion. -/
theorem finite_rank_approximation [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I)
    (hfinite : entropyRoof Phi.val rho.coefficients < ⊤) :
    ∃ rhoSeq : ℕ → State I, Tendsto rhoSeq atTop (nhds rho) ∧
      (∀ n, (∃ r, RankAtMost (rhoSeq n).coefficients r) ∧
        extendedEntropyNats (Phi.val (rhoSeq n).coefficients) < ⊤) ∧
      Tendsto (fun n => entropyRoof Phi.val (rhoSeq n).coefficients) atTop
        (nhds (entropyRoof Phi.val rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
