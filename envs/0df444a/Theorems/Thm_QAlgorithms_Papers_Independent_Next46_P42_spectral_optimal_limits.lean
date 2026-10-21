-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_spectral_optimal_limits
-- name    : QAlgorithms.Papers.Independent.Next46.P42.spectral_optimal_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:48:06.602978+00:00
-- url     : https://prove2.me/theorems/10e56378-2345-4940-a75d-4f03cb018e6c
-- title:
--   §5, Corollary 4: spectral truncations of optimal measures
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Assume $H_\Phi(\rho)<+\infty$. For the normalized truncations $\rho_n$ retaining the largest $n+1$ eigenvalues, choose pure-supported roof-optimal laws $\mu_n$ represented by at most $(n+1)^2$ labelled slots. Then
--   $$
--   \varnothing\ne\operatorname{LimSubseq}(\mu_n)
--   \subseteq\{\mu:\mu\text{ is both roof-optimal and chi-optimal for }\rho\}.
--   $$
--   The first spectral mass is positive; finite-rank states are retained after their last positive eigenvalue. Limits are weak subsequential limits. This obtains optimizers at the target from optimizers at spectral approximants.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 17, §5, Corollary 4: spectral truncations of optimal measures

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

/-- PDF pp.17–18, Corollary 4: every weak subsequential limit is optimal for both
functionals. There is no demand for convergence of the whole sequence. -/
theorem spectral_optimal_limits [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I)
    (hfinite : extendedEntropyNats (Phi.val rho.coefficients) < ⊤)
    (s : SpectralPresentation rho) (horder : Antitone s.weight)
    (mu : ℕ → GeneralizedEnsemble I)
    (hopt : ∀ n, RoofOptimal Phi.val (spectralTruncation s n) (mu n))
    (hsize : ∀ n, ∃ (m : ℕ) (e : LabelledEnsemble I m), m ≤ (n+1)^2 ∧
      (∀ i, e.state i ∈ pureStates I) ∧ e.average = spectralTruncation s n ∧
      (mu n : Measure (State I)) = e.law) :
    (partialLimits mu).Nonempty ∧ ∀ nu ∈ partialLimits mu,
      RoofOptimal Phi.val rho.coefficients nu ∧ ChiOptimal Phi.val rho.coefficients nu := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
