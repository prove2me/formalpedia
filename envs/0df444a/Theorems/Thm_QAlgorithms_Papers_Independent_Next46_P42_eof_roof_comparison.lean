-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_eof_roof_comparison
-- name    : QAlgorithms.Papers.Independent.Next46.P42.eof_roof_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:53:13.041481+00:00
-- url     : https://prove2.me/theorems/eeb70383-ec16-4186-8409-296145517a89
-- title:
--   §7, comparison of countable and measure EoF roofs
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   Let $E_F^1$ be the infimum of $\sum_i p_iH(\operatorname{Tr}_B\psi_i)$ over countable decompositions into normalized pure density operators, with nonnegative summable probabilities of total mass one and trace-norm convergent average $\rho$. For every bipartite state,
--   $$
--   E_F^2(\rho)\le E_F^1(\rho).
--   $$
--   No entropy finiteness or Gaussian assumption is imposed. This compares the full-state measure and countable roofs.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 22, §7, comparison of countable and measure EoF roofs

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

/-- PDF p.22: comparison of countable and measure roofs on every state. -/
theorem eof_roof_comparison [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    (rho : State (I × K)) :
    measureEof rho.coefficients ≤ countableEof rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
