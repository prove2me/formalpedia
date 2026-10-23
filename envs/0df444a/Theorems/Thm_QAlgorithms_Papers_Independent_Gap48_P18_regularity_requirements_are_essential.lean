-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_regularity_requirements_are_essential
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.regularity_requirements_are_essential
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:53:44.435494+00:00
-- url     : https://prove2.me/theorems/a9409f26-9265-4141-b4b9-de19a9574e42
-- title:
--   Remark 5
-- statement:
--   A decreasing family of nonempty closed subsets of a regular finite-capacity set, all with the same capacity as that set, must have capacities converging to the capacity of its intersection. Thus a failure of this conclusion certifies nonregularity. Also there exists a nonempty closed finite-capacity set $A$ such that
--
--   $$\text{no closed subset of }A\text{ is minimal among those of capacity }\bar C(A).$$
--
--   These assertions show why the regularity requirements in Theorem 2G and 2I cannot simply be dropped.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 31, Remark 5

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

/-- Remark 5, arXiv:quant-ph/0510073v2, PDF pp.31.
 -/
theorem regularity_requirements_are_essential {I : Type} [Countable I] [Infinite I] :
    (∀ (A : Set (State I)) (hA : A.Nonempty), setChiCapacity A < ⊤ → ChiRegular A →
      ∀ (B : ℕ → Set (State I)),
        (∀ n, (B n).Nonempty ∧ IsClosed (B n) ∧ B n ⊆ A ∧ setChiCapacity (B n) = setChiCapacity A) →
        (∀ n, B (n + 1) ⊆ B n) →
        Tendsto (fun n => setChiCapacity (B n)) atTop (𝓝 (setChiCapacity (⋂ n, B n)))) ∧
      (∃ A : Set (State I), A.Nonempty ∧ IsClosed A ∧ setChiCapacity A < ⊤ ∧
        ¬ ∃ B, MinimalClosedEqualCapacity A B) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
