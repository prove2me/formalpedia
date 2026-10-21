-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_chi_entropy_roof_identity
-- name    : QAlgorithms.Papers.Independent.Next46.P42.chi_entropy_roof_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:46:01.758005+00:00
-- url     : https://prove2.me/theorems/1b2f4285-c7ed-4ea4-a48f-3d287ebc0a71
-- title:
--   §5, equation (15) and its infinite-output extension
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For every input state, the following two cases hold:
--   $$
--   H_\Phi(\rho)<+\infty\Longrightarrow
--   \chi_\Phi(\rho)=H_\Phi(\rho)-\widehat H_\Phi(\rho),
--   $$
--   $$
--   H_\Phi(\rho)=+\infty,\quad\widehat H_\Phi(\rho)<+\infty
--   \Longrightarrow\chi_\Phi(\rho)=+\infty.
--   $$
--   The first subtraction is between finite nonnegative values, and the second case avoids infinity minus infinity. This is the entropy–chi–roof identity on its stated domains.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 16, §5, equation (15) and its infinite-output extension

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

/-- PDF p.16, (15): finite-output subtraction and the separate infinite-output/finite-roof case. -/
theorem chi_entropy_roof_identity [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (Phi : Channel I J) (rho : State I) :
    (extendedEntropyNats (Phi.val rho.coefficients) < ⊤ →
      stateChi Phi.val rho = extendedEntropyNats (Phi.val rho.coefficients) -
        entropyRoof Phi.val rho.coefficients) ∧
    (extendedEntropyNats (Phi.val rho.coefficients) = ⊤ →
      entropyRoof Phi.val rho.coefficients < ⊤ → stateChi Phi.val rho = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
