-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_bounded_entropy_zero_decrease_continuous
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.bounded_entropy_zero_decrease_continuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:56:16.255751+00:00
-- url     : https://prove2.me/theorems/2a12296f-3cc5-4cae-adae-4b12c87951d5
-- title:
--   Remark 6
-- statement:
--   Let $A$ be a nonempty closed convex set of states, each with zero decrease coefficient. Boundedness of entropy on $A$ implies
--
--   $$H\big|_A\ \text{is finite and continuous}.$$
--
--   The Gaussian-state parenthesis in the source is an illustration, not an additional Gaussian theorem.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 35, Remark 6

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

/-- Remark 6, arXiv:quant-ph/0510073v2, PDF pp.35.
 -/
theorem bounded_entropy_zero_decrease_continuous {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hconvex : CoefficientConvexStates A) (hbounded : entropySup A < ⊤)
    (hdecrease : ∀ rho ∈ A, decreaseCoefficient rho = 0) :
    FiniteContinuousOn stateEntropyNats A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
