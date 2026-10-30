-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_energyNorm_tensorChannel
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.energyNorm_tensorChannel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:27:17.280905+00:00
-- url     : https://prove2.me/theorems/8416512c-b394-49b0-8a40-46e2af303dc7
-- title:
--   Lemma 4(5)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\Delta:A\to B$ be a source superoperator and $\mathcal T:C\to C$ a CPTP map. Give $A,C$ grounded Hamiltonians $H_A,H_C$. For every $E>0$, $$\|\Delta\|_{\diamond E,H_A}=\|\Delta\otimes\mathcal T\|_{\diamond E,H_A\otimes I+I\otimes H_C}.$$ The joint energy is the sum of the two input-marginal expectations. This is stability under an independent channel when the joint input budget is additive.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 5, Lemma 4(5)

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

/-- Lemma 4(5), PDF p.5: adjoining any channel preserves the norm when the
joint input budget uses the additive Hamiltonian. Both forms are grounded. -/
theorem energyNorm_tensorChannel {I J K : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] [Countable K] [Nonempty K]
    (H : PositiveObservable I) (G : PositiveObservable K) (hH : Grounded H) (hG : Grounded G)
    (D : Matrix I I ℂ → Matrix J J ℂ) (hD : IsSuperoperator D) (T : Channel K K)
    (E : ℝ) (hE : 0 < E) :
    energyMagnitude H E D =
      constrainedMagnitude (tensorSumEnergy H G) E (channelTensorAction D T.val) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
