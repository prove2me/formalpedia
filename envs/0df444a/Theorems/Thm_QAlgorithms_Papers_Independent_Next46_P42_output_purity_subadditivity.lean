-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P42_output_purity_subadditivity
-- name    : QAlgorithms.Papers.Independent.Next46.P42.output_purity_subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:51:15.062236+00:00
-- url     : https://prove2.me/theorems/106bf1c6-5adc-4d54-8ea8-573dba0eee68
-- title:
--   §6, equation (18): output-purity subadditivity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, with the trace-norm topology. Entropies use natural logarithms and take values in $[0,+\infty]$. Channels are arbitrary completely positive trace-preserving maps on trace class. Write $H_\Phi(\rho)=H(\Phi(\rho))$, $\chi_\Phi$ for the finite-ensemble relative-entropy supremum at exact average $\rho$, $\widehat H_\Phi$ for the infimum of integrated output entropy over all Borel probability laws with exact barycenter, and $\operatorname{conv}H_\Phi$ for the corresponding finite mixed-ensemble infimum.
--
--   For arbitrary channels $\Phi,\Psi$ and bounded positive input observables $A,B$,
--   $$
--   \nu_H(\Phi\otimes\Psi,A\otimes I+I\otimes B)
--   \le\nu_H(\Phi,A)+\nu_H(\Psi,B).
--   $$
--   The joint infimum ranges over all states, and the Kronecker-sum cost is $\operatorname{Tr}A\omega_H+\operatorname{Tr}B\omega_K$. Values may be infinite. This is the unconditional one-sided tensor inequality.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, PDF p. 18, §6, equation (18): output-purity subadditivity

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

/-- PDF p.18, (18): unconditional one-sided output-purity subadditivity. -/
theorem output_purity_subadditivity [Countable I] [Nonempty I] [Countable J] [Nonempty J] [Countable K] [Nonempty K] [Countable L] [Nonempty L]
    (Phi : Channel I J) (Psi : Channel K L)
    (A : BoundedPositiveObservable I) (B : BoundedPositiveObservable K) :
    minimumCost (channelTensorAction Phi.val Psi.val) (kroneckerCost A B) ≤
      outputPurity Phi.val A + outputPurity Psi.val B := by sorry

end QAlgorithms.Papers.Independent.Next46.P42

end
