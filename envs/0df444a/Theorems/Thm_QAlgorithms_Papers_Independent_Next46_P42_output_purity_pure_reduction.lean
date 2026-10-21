-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_output_purity_pure_reduction
-- name    : QAlgorithms.Papers.Independent.Next46.P42.output_purity_pure_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:50:36.037979+00:00
-- url     : https://prove2.me/theorems/93552a96-e5eb-42d6-82e5-2baef4d02f9d
-- title:
--   §6, pure-state reduction of output-purity infima
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For every bounded positive $A$, including zero, the two extended infima may be restricted to normalized pure states:
--   $$
--   \nu_H(\Phi,A)=\inf_{\rho\ \mathrm{pure}}[H_\Phi(\rho)+\operatorname{Tr}A\rho],
--   \qquad H_{\min}(\Phi)=\inf_{\rho\ \mathrm{pure}}H_\Phi(\rho).
--   $$
--   Here $H_{\min}$ is the output-entropy infimum over all input states. Neither infimum is assumed attained or finite. This gives the pure-state reductions stated after equations (16) and (17).
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 18, §6, pure-state reduction of output-purity infima

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

/-- PDF p.18, after (17): both infima may be taken over pure states; neither is assumed attained. -/
theorem output_purity_pure_reduction [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (A : BoundedPositiveObservable I) :
    outputPurity Phi.val A =
      (⨅ psi : PureState I, extendedEntropyNats (Phi.val psi.val.coefficients) +
        closedFormExpectation A.val psi.val.coefficients) ∧
    minimumOutputEntropy Phi.val =
      ⨅ psi : PureState I, extendedEntropyNats (Phi.val psi.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
