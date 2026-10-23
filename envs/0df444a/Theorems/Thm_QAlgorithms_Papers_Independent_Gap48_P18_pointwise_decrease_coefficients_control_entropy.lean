-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_pointwise_decrease_coefficients_control_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.pointwise_decrease_coefficients_control_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:55:34.024128+00:00
-- url     : https://prove2.me/theorems/3611a918-16ca-453f-8bfe-5fd060fd4ba5
-- title:
--   Corollary 6
-- statement:
--   Let $A$ be a nonempty closed convex finite-capacity set. If every $\rho\in A$ has $\operatorname{dc}(\rho)<1$, then $A$ is regular and entropy is bounded on $A$. If every decrease coefficient is zero, then
--
--   $$H\big|_A\ \text{is finite and continuous}.$$
--
--   These are pointwise assumptions; no uniform gap of the coefficients below one is imposed.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 34, Corollary 6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 6, arXiv:quant-ph/0510073v2, PDF pp.34.
 -/
theorem pointwise_decrease_coefficients_control_entropy {I : Type}
    [Countable I] [Nonempty I] (A : Set (State I)) (hA : A.Nonempty)
    (hclosed : IsClosed A) (hconvex : CoefficientConvexStates A) (hfinite : setChiCapacity A < ⊤) :
    ((∀ rho ∈ A, decreaseCoefficient rho < 1) → ChiRegular A ∧ entropySup A < ⊤) ∧
      ((∀ rho ∈ A, decreaseCoefficient rho = 0) → FiniteContinuousOn stateEntropyNats A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
