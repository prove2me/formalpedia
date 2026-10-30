-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_outputEnergy_envelope
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.outputEnergy_envelope
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:29:47.054725+00:00
-- url     : https://prove2.me/theorems/a1f78b09-bb80-43ee-b537-ae4211dd613a
-- title:
--   §V unnumbered: concave output-energy envelope
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\mathcal N_1,\mathcal N_2:A\to B$ be channels. Define $$f_i(E)=\sup_{\rho:\operatorname{Tr}\rho H_A\le E}\operatorname{Tr}\mathcal N_i(\rho)H_B,\qquad E\ge0.$$ If both functions are finite at every nonnegative budget, they are nondecreasing and concave. There exist common finite $\alpha,E_0\ge0$ such that $$f_i(E)\le\alpha E+E_0\quad(i=1,2;\ E\ge0),\qquad \operatorname{Tr}\mathcal N_i(\rho)H_B\le\alpha\operatorname{Tr}\rho H_A+E_0$$ for every finite-energy input state. The latter is the form-inequality interpretation of the printed unbounded Heisenberg notation. This supplies common affine energy limits.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 9, §V unnumbered: concave output-energy envelope

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

/-- Section V, PDF p.9: the two finite output-energy envelopes are monotone
and concave, and admit common affine bounds. The form-inequality meaning of the
unbounded Heisenberg notation is stated by actual expectations. Grounding does
not add an attained ground vector; an empty zero-budget supremum is zero. -/
theorem outputEnergy_envelope {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (G : PositiveObservable J)
    (hH : Grounded H) (hG : Grounded G) (N M : Channel I J)
    (hfiniteN : ∀ E : ℝ, 0 ≤ E → outputEnergyEnvelope H G N.val E < ⊤)
    (hfiniteM : ∀ E : ℝ, 0 ≤ E → outputEnergyEnvelope H G M.val E < ⊤) :
    (MonotoneOn (fun E => (outputEnergyEnvelope H G N.val E).toReal) (Set.Ici 0) ∧
     ConcaveOn ℝ (Set.Ici 0) (fun E => (outputEnergyEnvelope H G N.val E).toReal)) ∧
    (MonotoneOn (fun E => (outputEnergyEnvelope H G M.val E).toReal) (Set.Ici 0) ∧
     ConcaveOn ℝ (Set.Ici 0) (fun E => (outputEnergyEnvelope H G M.val E).toReal)) ∧
    ∃ alpha offset : ℝ, 0 ≤ alpha ∧ 0 ≤ offset ∧
      AffineEnergyLimited H G alpha offset N.val ∧ AffineEnergyLimited H G alpha offset M.val ∧
      (∀ E : ℝ, 0 ≤ E → outputEnergyEnvelope H G N.val E ≤ ENNReal.ofReal (alpha * E + offset) ∧
        outputEnergyEnvelope H G M.val E ≤ ENNReal.ofReal (alpha * E + offset)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
