-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_lemma_1_16
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_16
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:56:38.65015+00:00
-- url     : https://prove2.me/theorems/ef285e08-521c-4584-bff5-e5408bb3e1e8
-- title:
--   Differentiability into arbitrary products
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $E$ and $(F_i)_{i\in I}$ Hausdorff topological $\mathbb K$-vector spaces, $U\subseteq E$ open, $f:U\to\prod_{i\in I}F_i$, and $k\in\mathbb N_0\cup\{\infty\}$. Equip the range with its product topology and write $\operatorname{pr}_i$ for its projections. Then
--
--   $$
--   f\in C^k_{\mathbb K}\quad\Longleftrightarrow\quad
--   (\forall i\in I)\ \operatorname{pr}_i\circ f\in C^k_{\mathbb K}.
--   $$
--
--   Thus all coordinates test regularity, including infinite regularity, with no finiteness restriction on the product. An empty index set is allowed.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 16, Lemma 1.16

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 1.16, PDF p.16: C^k regularity into an arbitrary cartesian product
with its product topology is equivalent to coordinatewise C^k regularity. -/
theorem lemma_1_16
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    {I : Type*} (Fi : I → Type w) [∀ i, AddCommGroup (Fi i)]
    [∀ i, Module K (Fi i)] [∀ i, TopologicalSpace (Fi i)]
    [∀ i, T2Space (Fi i)] [∀ i, IsTopologicalAddGroup (Fi i)]
    [∀ i, ContinuousSMul K (Fi i)]
    (U : Set E) (hU : IsOpen U) (f : U → ∀ i, Fi i) (k : WithTop ℕ) :
    bgnCr K (∀ i, Fi i) k U f ↔
      ∀ i, bgnCr K (Fi i) k U (fun x => f x i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
