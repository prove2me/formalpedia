-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_duality_additivity
-- name    : QAlgorithms.Papers.Independent.Next46.P42.duality_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:33:55.638372+00:00
-- url     : https://prove2.me/theorems/7f853c0c-fc44-45c7-ab54-e04a307e5a17
-- title:
--   §6, unnumbered Theorem: convex-duality additivity equivalence and consequences
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For channels $\Phi,\Psi$, let (i) be strong roof superadditivity on every joint state $\omega$, with marginals $\omega_H,\omega_K$, and let (ii) be output-purity additivity for all bounded positive observables $A,B$, including zero. Define $\nu_H(\Phi,A)=\inf_\rho[H_\Phi(\rho)+\operatorname{Tr}A\rho]$. Then
--   $$
--   \text{(i)}\Longleftrightarrow\text{(ii)},\qquad
--   \text{(i)}\Longrightarrow\text{(iii)}\land\text{(iv)}\land\text{(v)}.
--   $$
--   Here (i) is $\widehat H_{\Phi\otimes\Psi}(\omega)\ge\widehat H_\Phi(\omega_H)+\widehat H_\Psi(\omega_K)$; (ii) is $\nu_H(\Phi\otimes\Psi,A\otimes I+I\otimes B)=\nu_H(\Phi,A)+\nu_H(\Psi,B)$; (iii) is $\widehat H_{\Phi\otimes\Psi}(\rho\otimes\sigma)=\widehat H_\Phi(\rho)+\widehat H_\Psi(\sigma)$ for every product input; (iv) is $\bar C(\Phi\otimes\Psi;\mathcal A\otimes\mathcal B)=\bar C(\Phi;\mathcal A)+\bar C(\Psi;\mathcal B)$ for every pair of nonempty constraints with pointwise finite output entropy, where the joint constraint allows every state with these marginal constraints; and (v) is minimum-output-entropy additivity for every pair of nonzero closed input-subspace restrictions. The constrained capacity $\bar C$ is optimized over finite ensembles whose average belongs to its constraint. This theorem relates conditional additivity properties; it does not assert their universal validity.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 19, §6, unnumbered Theorem: convex-duality additivity equivalence and consequences

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

/-- PDF pp.19–20, unnumbered Theorem: all five clauses, conditionally.
The p.20 duplicated Phi subscript is read as Psi, as in the p.19 statement. -/
theorem duality_additivity [Countable I] [Nonempty I] [Countable J] [Nonempty J] [Countable K] [Nonempty K] [Countable L] [Nonempty L]
    (Phi : Channel I J) (Psi : Channel K L) :
    (StrongSuperadditive Phi.val Psi.val ↔ PurityAdditive Phi.val Psi.val) ∧
    (StrongSuperadditive Phi.val Psi.val →
      (∀ (rho : State I) (sigma : State K),
        entropyRoof (channelTensorAction Phi.val Psi.val) (productCoeff rho.coefficients sigma.coefficients) =
          entropyRoof Phi.val rho.coefficients + entropyRoof Psi.val sigma.coefficients) ∧
      StrongCapacityAdditive Phi.val Psi.val ∧ SubchannelMinimumAdditive Phi.val Psi.val) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
