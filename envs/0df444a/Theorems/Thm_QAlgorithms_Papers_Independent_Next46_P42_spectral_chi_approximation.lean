-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_spectral_chi_approximation
-- name    : QAlgorithms.Papers.Independent.Next46.P42.spectral_chi_approximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:37:26.927794+00:00
-- url     : https://prove2.me/theorems/fddc5cbd-5f1d-4745-9d68-eca275d2c71d
-- title:
--   §3, Remark: spectral finite-rank approximation of χ
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For any state $\rho$, take a nonincreasing spectral decomposition with zero padding after its finite rank. Let $P_n$ retain the first $n+1$ eigenvalues, starting with a positive one, and put $\rho_n=(\operatorname{Tr}P_n\rho)^{-1}P_n\rho$. Then every $\rho_n$ is a normalized state of rank at most $n+1$ and
--   $$
--   \chi_\Phi(\rho_n)\longrightarrow\chi_\Phi(\rho).
--   $$
--   Finite-rank states remain unchanged after all their positive eigenvalues are included. The result allows approximation of an infinite chi value.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 8, §3, Remark: spectral finite-rank approximation of χ

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

/-- PDF p.8, Remark: leading positive spectral truncations, with n+1 indexing.
Finite-rank states are retained once all positive eigenvalues have been included. -/
theorem spectral_chi_approximation [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I)
    (s : SpectralPresentation rho) (horder : Antitone s.weight) :
    (∀ n, IsDensity (spectralTruncation s n) ∧ RankAtMost (spectralTruncation s n) (n+1)) ∧
    Tendsto (fun n => finiteEnsembleCapacity Phi.val {sigma : State I | sigma.coefficients = spectralTruncation s n}) atTop
      (nhds (stateChi Phi.val rho)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
