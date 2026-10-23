-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_increasing_union_relatively_compact
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.increasing_union_relatively_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:39:05.311925+00:00
-- url     : https://prove2.me/theorems/a2d80c9f-f8b6-45af-b50c-d12399b97476
-- title:
--   Corollary 7
-- statement:
--   Let $A_n\subseteq A_{n+1}$ be sets of density states. If one finite constant $M$, independent of $n$, satisfies $\bar C(A_n)\le M$ for every $n$, then
--
--   $$\overline{\bigcup_n A_n}\ \text{is compact in trace norm}.$$
--
--   Thus a uniform capacity bound gives relative compactness of the entire increasing union.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 35, Corollary 7

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

/-- Corollary 7, arXiv:quant-ph/0510073v2, PDF pp.35.
 -/
theorem increasing_union_relatively_compact {I : Type} [Countable I] [Nonempty I]
    (A : ℕ → Set (State I)) (hmono : ∀ n, A n ⊆ A (n + 1))
    (M : ℝ≥0∞) (hM : M < ⊤) (hbound : ∀ n, setChiCapacity (A n) ≤ M) :
    IsCompact (closure (⋃ n, A n)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
