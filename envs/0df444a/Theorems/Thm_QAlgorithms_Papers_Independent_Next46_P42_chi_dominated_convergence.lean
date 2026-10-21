-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_chi_dominated_convergence
-- name    : QAlgorithms.Papers.Independent.Next46.P42.chi_dominated_convergence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:36:42.876875+00:00
-- url     : https://prove2.me/theorems/6f0ab923-cee4-4b1f-a48f-d01807cc40c3
-- title:
--   §3, Corollary 1: dominated convergence of χ
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Suppose $\rho_n\to\rho$ in trace norm and real numbers $\lambda_n>0$ satisfy $\lambda_n\to1$ and $\lambda_n\rho_n\le\rho$ in operator order for every $n$. Then
--   $$
--   \lim_{n\to\infty}\chi_\Phi(\rho_n)=\chi_\Phi(\rho).
--   $$
--   The limit may be infinite, and $\lambda_n=1$ is allowed. This is the dominated convergence principle for the chi function.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 8, §3, Corollary 1: dominated convergence of χ

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

/-- PDF p.8, Corollary 1: positive domination factors may equal one. -/
theorem chi_dominated_convergence [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I)
    (rhoSeq : ℕ → State I) (hseq : Tendsto rhoSeq atTop (nhds rho))
    (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hwlim : Tendsto w atTop (nhds 1))
    (hdom : ∀ n, TraceOperatorLE ((w n : ℂ) • (rhoSeq n).coefficients) rho.coefficients) :
    Tendsto (fun n => stateChi Phi.val (rhoSeq n)) atTop
      (nhds (stateChi Phi.val rho)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
