-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_roof_fenchel_formula
-- name    : QAlgorithms.Papers.Independent.Next46.P42.roof_fenchel_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:44:45.883168+00:00
-- url     : https://prove2.me/theorems/3e00a8cb-ffed-481c-976b-db655249e4c4
-- title:
--   §4, Corollary 2: Fenchel biconjugate and max–min formula
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For a bounded Hermitian observable $A$, define the signed extended conjugate $H_\Phi^*(A)=\sup_\sigma[\operatorname{Tr}A\sigma-H_\Phi(\sigma)]$ and its biconjugate $H_\Phi^{**}(\rho)=\sup_A[\operatorname{Tr}A\rho-H_\Phi^*(A)]$. Then
--   $$
--   \widehat H_\Phi(\rho)=H_\Phi^{**}(\rho)
--   =\sup_{A\in\mathfrak B_h(\mathcal H)}\inf_{\sigma\in\mathfrak S(\mathcal H)}
--   \bigl[H_\Phi(\sigma)+\operatorname{Tr}A(\rho-\sigma)\bigr].
--   $$
--   All signed operations take place in the extended real line. No supremum or infimum is asserted attained, and identically infinite output entropy is allowed. This is the source’s dual description of the roof.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 15, §4, Corollary 2: Fenchel biconjugate and max–min formula

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

/-- PDF p.15, Corollary 2: signed extended biconjugate and sup-inf formula,
including the identically infinite output-entropy case. -/
theorem roof_fenchel_formula [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I) :
    (entropyRoof Phi.val rho.coefficients).toEReal = entropyBiconjugate Phi.val rho.coefficients ∧
    entropyBiconjugate Phi.val rho.coefficients =
      ⨆ A : HermitianObservable I, ⨅ sigma : State I,
        (extendedEntropyNats (Phi.val sigma.coefficients)).toEReal +
          (observablePair A.val (rho.coefficients - sigma.coefficients) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
