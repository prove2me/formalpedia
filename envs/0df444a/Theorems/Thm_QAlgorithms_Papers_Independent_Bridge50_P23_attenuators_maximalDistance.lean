-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_attenuators_maximalDistance
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.attenuators_maximalDistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:21:50.763823+00:00
-- url     : https://prove2.me/theorems/65c82d07-f8a4-4e97-ba80-8ba0598b51bb
-- title:
--   Proposition 1: distinct attenuators have maximum diamond distance
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. Let $\mathcal A_\eta$ be the single-mode quantum-limited vacuum attenuator with complex amplitude $\eta$, characterized by $\mathcal A_\eta(|\alpha\rangle\langle\alpha|)=|\eta\alpha\rangle\langle\eta\alpha|$ on coherent states. For $|\eta|,|\eta'|\le1$ with $\eta\ne\eta'$, $$\|\mathcal A_\eta-\mathcal A_{\eta'}\|_\diamond=2.$$ This shows that arbitrarily nearby amplitude parameters can have maximal unrestricted channel distance.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 2, Proposition 1: distinct attenuators have maximum diamond distance

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P23

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P23

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsTraceClass traceSize tensorApply rankOne productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel traceSecond traceFirst homogeneousEntropy generalizedRelativeEntropy
   channelTensorAction finiteInputCoherentInfo)

open QAlgorithms.Papers.Independent.Frontier18.P08 (IsQuantumOperation)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation GibbsCondition TensorBlockIndex blockAction blockEnergy)

open QAlgorithms.Papers.Independent.Claimed50.P18 (finiteFirstConditionalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, PDF pp.2--3: distinct complex amplitudes in the closed
unit disc give distance two, including zero and lossless endpoints. -/
theorem attenuators_maximalDistance (eta zeta : ℂ) (heta : ‖eta‖ ≤ 1)
    (hzeta : ‖zeta‖ ≤ 1) (hne : eta ≠ zeta) :
    diamondMagnitude (fun X => vacuumAttenuator eta X - vacuumAttenuator zeta X) = 2 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
