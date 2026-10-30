-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_pureState_reduction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.pureState_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:20:44.631096+00:00
-- url     : https://prove2.me/theorems/be28992d-7847-403e-a1a8-9647eb3a87b4
-- title:
--   §I and §III, unnumbered: pure probes and a copy reference
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\Delta$ be a complex-linear Hermitian-preserving map in the real span of bounded completely positive maps on trace class. If $A'$ is a copy of $A$, then $$\|\Delta\|_\diamond=\sup_{\psi\text{ pure on }AA'}\|(\Delta\otimes\mathrm{id})(\psi)\|_1.$$ When $A$ is finite dimensional, this supremum is attained by a pure state. For every grounded $H_A$ and $E>0$, $$\|\Delta\|_{\diamond E}=\sup_{\substack{\psi\text{ pure on }AA'\\\operatorname{Tr}\psi^A H_A\le E}}\|(\Delta\otimes\mathrm{id})(\psi)\|_1.$$ These reductions allow pure probes on a copy reference; constrained attainment is not asserted.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 1, §I and §III, unnumbered: pure probes and a copy reference

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

/-- Sections I and III, PDF pp.1,4: pure-state/copy-reference reductions;
only the unrestricted norm has the finite-input-dimensional attainment clause. -/
theorem pureState_reduction {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (D : Matrix I I ℂ → Matrix J J ℂ)
    (hD : IsSuperoperator D) (H : PositiveObservable I) (hH : Grounded H)
    (E : ℝ) (hE : 0 < E) :
    diamondMagnitude D = (⨆ rho : PureState (I × I),
      traceSize (tensorApply D rho.val.coefficients)) ∧
    (Finite I → ∃ rho : PureState (I × I),
      traceSize (tensorApply D rho.val.coefficients) = diamondMagnitude D) ∧
    energyMagnitude H E D = pureEnergyMagnitude H E D := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
