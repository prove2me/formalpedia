-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_marginal_set_convexity_and_compactness
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.marginal_set_convexity_and_compactness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T08:01:26.008995+00:00
-- url     : https://prove2.me/theorems/68b303da-22f4-4e2f-917f-6d89aa0c5e93
-- title:
--   Marginal constraints: convexity and compactness equivalences
-- statement:
--   Let A and B be nonempty subsets of the normalized state spaces of nonzero separable complex Hilbert spaces H and K. Define A tensor B to be all joint states on H tensor K whose first marginal belongs to A and whose second marginal belongs to B. This joint constraint set is convex if and only if both A and B are convex, and it is compact in trace norm if and only if both A and B are compact in trace norm.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 61, Lemma 8 (continues p.62)

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

/-- Lemma 8, arXiv:quant-ph/0510073v2, PDF pp.61-62, cited there from [17].
Printed: the two equivalences for arbitrary marginal constraint sets.
Changed: make nonemptiness of both marginal sets explicit, as required by the
source's reverse implications. Why: an empty first set gives an empty compact
convex joint set for any second set, including nonconvex or noncompact ones.
This records the source's implicit nonempty-set convention and retains both
clauses. Singleton marginal sets give a nonvacuous instance. -/
theorem marginal_set_convexity_and_compactness {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (A : Set (State I)) (B : Set (State J)) (hA : A.Nonempty) (hB : B.Nonempty) :
    (CoefficientConvexStates (jointMarginalConstraintSet A B) ↔
      CoefficientConvexStates A ∧ CoefficientConvexStates B) ∧
    (IsCompact (jointMarginalConstraintSet A B) ↔ IsCompact A ∧ IsCompact B) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
