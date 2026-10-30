-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_energyNorm_budgetDependence
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.energyNorm_budgetDependence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:25:41.383251+00:00
-- url     : https://prove2.me/theorems/f6608b63-b9fb-497a-a0af-6b0b9cd1cafb
-- title:
--   Lemma 4(2)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. For every source superoperator $\Delta$, the function $E\mapsto\|\Delta\|_{\diamond E}$ is nondecreasing and concave on $(0,\infty)$. In particular, for $0<E<E'$, $$\|\Delta\|_{\diamond E}\le\|\Delta\|_{\diamond E'}\le\frac{E'}{E}\|\Delta\|_{\diamond E}.$$ All positive-budget norms induce the same topology on superoperators. This permits changing the testing budget without changing convergence.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 5, Lemma 4(2)

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

/-- Lemma 4(2), PDF p.5: monotonicity, concavity, both comparison inequalities,
and equality of the norm topologies at any two positive budgets. -/
theorem energyNorm_budgetDependence {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (hH : Grounded H)
    (D : Matrix I I ℂ → Matrix J J ℂ) (hD : IsSuperoperator D) :
    MonotoneOn (fun E => (energyMagnitude H E D).toReal) (Set.Ioi 0) ∧
    ConcaveOn ℝ (Set.Ioi 0) (fun E => (energyMagnitude H E D).toReal) ∧
    (∀ E F : ℝ, 0 < E → E < F →
      energyMagnitude H E D ≤ energyMagnitude H F D ∧
      energyMagnitude H F D ≤ ENNReal.ofReal (F / E) * energyMagnitude H E D) ∧
    (∀ E F : ℝ, 0 < E → 0 < F →
      energyNormTopology (J := J) H E = energyNormTopology (J := J) H F) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
