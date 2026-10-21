-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_continuity_and_optimal_limits
-- name    : QAlgorithms.Papers.Independent.Next46.P42.continuity_and_optimal_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:46:46.65085+00:00
-- url     : https://prove2.me/theorems/9784ff07-298f-4610-97ba-9251eb1132e3
-- title:
--   §5, Proposition 7: continuity and limits of optimal measures
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   If $H_\Phi$ is finite valued and continuous on a subset $\mathcal A$ in the relative trace-norm topology, both $\chi_\Phi$ and $\widehat H_\Phi$ are continuous there. Moreover, if $\rho_n\to\rho$ in trace norm, $\widehat H_\Phi(\rho_n)\to\widehat H_\Phi(\rho)$, and $\mu_n$ is a pure-supported roof-optimal law for $\rho_n$, then
--   $$
--   \varnothing\ne\operatorname{LimSubseq}(\mu_n)
--   \subseteq\{\mu:\mu\text{ is roof-optimal for }\rho\}.
--   $$
--   Subsequence limits use weak convergence of probability laws. The second assertion permits an infinite limiting roof and does not assert convergence of the entire optimizer sequence. This links entropy continuity and stability of optimizing laws.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 16, §5, Proposition 7: continuity and limits of optimal measures

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

/-- PDF pp.16–17, Proposition 7: finite-valued entropy continuity in the first
clause; the optimizer limit clause permits an infinite limiting roof. -/
theorem continuity_and_optimal_limits [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) :
    (∀ A : Set (State I),
      (∀ rho ∈ A, extendedEntropyNats (Phi.val rho.coefficients) < ⊤) →
      ContinuousOn (fun rho : State I => (extendedEntropyNats (Phi.val rho.coefficients)).toReal) A →
      ContinuousOn (fun rho : State I => stateChi Phi.val rho) A ∧
      ContinuousOn (fun rho : State I => entropyRoof Phi.val rho.coefficients) A) ∧
    (∀ (rhoSeq : ℕ → State I) (rho : State I) (mu : ℕ → GeneralizedEnsemble I),
      Tendsto rhoSeq atTop (nhds rho) →
      Tendsto (fun n => entropyRoof Phi.val (rhoSeq n).coefficients) atTop
        (nhds (entropyRoof Phi.val rho.coefficients)) →
      (∀ n, RoofOptimal Phi.val (rhoSeq n).coefficients (mu n)) →
      (partialLimits mu).Nonempty ∧
        ∀ nu ∈ partialLimits mu, RoofOptimal Phi.val rho.coefficients nu) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
