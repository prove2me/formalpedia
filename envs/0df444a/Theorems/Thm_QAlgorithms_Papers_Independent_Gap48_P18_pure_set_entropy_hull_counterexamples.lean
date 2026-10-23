-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_pure_set_entropy_hull_counterexamples
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.pure_set_entropy_hull_counterexamples
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:47:01.608507+00:00
-- url     : https://prove2.me/theorems/34be0a3f-b5b2-4cea-a355-133e572e7c4e
-- title:
--   Remark 3
-- statement:
--   On an infinite-dimensional separable Hilbert space, the set $P$ of all pure states is closed, entropy is finite and continuous on $P$, and $\overline{\operatorname{co}}P$ is the full state space, where entropy is not finite continuous. Moreover there exists a countable compact pure-state set $A$ with
--
--   $$\sup_{\rho\in\overline{\operatorname{co}}A}H(\rho)=\infty.$$
--
--   Thus entropy continuity on a closed set alone does not control its closed convex hull.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 20, Remark 3

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

/-- Remark 3, arXiv:quant-ph/0510073v2, PDF pp.20.
 -/
theorem pure_set_entropy_hull_counterexamples {I : Type} [Countable I] [Infinite I] :
    IsClosed (pureStates I) ∧ FiniteContinuousOn stateEntropyNats (pureStates I) ∧
      stateClosedConvexHull (pureStates I) = Set.univ ∧
      ¬ FiniteContinuousOn stateEntropyNats (stateClosedConvexHull (pureStates I)) ∧
      ∃ A : Set (State I), A.Countable ∧ IsCompact A ∧ A ⊆ pureStates I ∧
        entropySup (stateClosedConvexHull A) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
