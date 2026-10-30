-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_attenuators_uniformContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.attenuators_uniformContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:28:11.417991+00:00
-- url     : https://prove2.me/theorems/f1d7737d-86f1-4afd-82e6-6b0bfa6c3ffb
-- title:
--   §IV.B unnumbered: uniform continuity of the attenuator family
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. Let $H=\sum_{n\ge0}n|n\rangle\langle n|$ be the number Hamiltonian and fix $E>0$. The complex-amplitude vacuum attenuator family is uniformly continuous on the closed unit disc: $$\forall a>0\ \exists d>0\ \forall |\eta|,|\eta'|\le1,\quad |\eta-\eta'|<d\Longrightarrow\|\mathcal A_\eta-\mathcal A_{\eta'}\|_{\diamond E}<a.$$ The distance threshold is uniform in both amplitudes, including zero and boundary points.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 8, §IV.B unnumbered: uniform continuity of the attenuator family

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

/-- Section IV.B, PDF p.8: uniform continuity on the entire compact complex
unit disc at every fixed positive number-energy budget; no invented modulus. -/
theorem attenuators_uniformContinuity (E : ℝ) (hE : 0 < E) :
    ∀ e : ℝ, 0 < e → ∃ d : ℝ, 0 < d ∧ ∀ eta zeta : ℂ,
      ‖eta‖ ≤ 1 → ‖zeta‖ ≤ 1 → ‖eta - zeta‖ < d →
      constrainedMagnitude numberEnergy E
        (fun X => vacuumAttenuator eta X - vacuumAttenuator zeta X) < ENNReal.ofReal e := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
