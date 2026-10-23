-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_optimal_measure_capacity_bounded_by_average_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.optimal_measure_capacity_bounded_by_average_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:42:33.549394+00:00
-- url     : https://prove2.me/theorems/51888b7b-d999-44c9-8d92-f12a00bea928
-- title:
--   Corollary 11
-- statement:
--   If a nonempty closed set $A$ has finite capacity and admits an optimal measure, then
--
--   $$\bar C(A)\le H(\Omega(A)).$$
--
--   The right side may be infinite. This is a necessary condition for existence of an optimal law.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 40, Corollary 11

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

/-- Corollary 11, arXiv:quant-ph/0510073v2, PDF pp.40.
 -/
theorem optimal_measure_capacity_bounded_by_average_entropy {I : Type}
    [Countable I] [Nonempty I] (A : Set (State I)) (hA : A.Nonempty)
    (hclosed : IsClosed A) (hfinite : setChiCapacity A < ⊤)
    (hoptimal : ∃ mu, OptimalMeasure A mu) :
    setChiCapacity A ≤ stateEntropyNats (optimalAverage A hA) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
