-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_output_energy_continuity
-- name    : QAlgorithms.Papers.Independent.Next46.P42.output_energy_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:47:21.566883+00:00
-- url     : https://prove2.me/theorems/b32d9a35-c62f-4842-a455-6959bd4fde8e
-- title:
--   §5, Corollary 3: output-energy constrained continuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Let $G$ be a positive unbounded output Hamiltonian with a complete orthonormal eigenbasis, nonnegative eigenvalues, finite spectral sublevels, and $\operatorname{Tr}e^{-\beta G}<+\infty$ for every real $\beta>0$. For each real $h\ge0$, both functions are continuous on
--   $$
--   \mathcal A_h=\{\rho:\operatorname{Tr}\Phi(\rho)G\le h\}.
--   $$
--   The energy is the extended nonnegative spectral sum in the eigenbasis, so it is imposed on the output and permits an empty constraint set. This supplies an explicit output-energy continuity domain.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 17, §5, Corollary 3: output-energy constrained continuity

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

/-- PDF p.17, Corollary 3: the energy constraint is on the output, for every h>=0. -/
theorem output_energy_continuity [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (G : OutputHamiltonian J)
    (hgibbs : G.gibbs) (h : ℝ) (hh : 0 ≤ h) :
    ContinuousOn (fun rho : State I => stateChi Phi.val rho)
      {rho | G.mean (Phi.val rho.coefficients) ≤ ENNReal.ofReal h} ∧
    ContinuousOn (fun rho : State I => entropyRoof Phi.val rho.coefficients)
      {rho | G.mean (Phi.val rho.coefficients) ≤ ENNReal.ofReal h} := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
