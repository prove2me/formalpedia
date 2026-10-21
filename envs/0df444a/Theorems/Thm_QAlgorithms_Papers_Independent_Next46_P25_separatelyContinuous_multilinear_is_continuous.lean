-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_separatelyContinuous_multilinear_is_continuous
-- name    : QAlgorithms.Papers.Independent.Next46.P25.separatelyContinuous_multilinear_is_continuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:00:38.054371+00:00
-- url     : https://prove2.me/theorems/882f03c4-11f9-498f-ad65-788d95138612
-- title:
--   Separately continuous multilinear maps on Fréchet products are continuous
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C\}$ and let $k\ge0$. Let $F_1,\ldots,F_k$ be Fréchet $\mathbb K$-spaces, let $V$ be a topological $\mathbb K$-vector space, and let $\beta:\prod_{i=1}^k F_i\to V$ be an algebraic multilinear map. Then
--
--   $$
--   \beta\text{ separately continuous}\quad\Longrightarrow\quad\beta\text{ jointly continuous}.
--   $$
--
--   Neither normability of the domains nor completeness or local convexity of the target is required. At $k=0$ the product is a singleton, so the map is constant and continuous. This is the full finite-product continuity assertion.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 15, Proposition 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proposition 4.3, PDF p.15: separate continuity implies joint
    continuity for algebraic multilinear maps with general Frechet domains.
    The target need not be normable or complete; k = 0 is allowed. -/
theorem separatelyContinuous_multilinear_is_continuous
    {K : Type u} [RCLike K] (k : ℕ) (F : Fin k → Type v)
    [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    [∀ i, UniformSpace (F i)] [∀ i, IsUniformAddGroup (F i)]
    [∀ i, T2Space (F i)] [∀ i, ContinuousSMul K (F i)]
    [∀ i, Module ℝ (F i)] [∀ i, IsScalarTower ℝ K (F i)]
    [∀ i, ContinuousSMul ℝ (F i)]
    [∀ i, LocallyConvexSpace ℝ (F i)]
    [∀ i, TopologicalSpace.MetrizableSpace (F i)] [∀ i, CompleteSpace (F i)]
    {V : Type w} [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V]
    (beta : MultilinearMap K F V) (hSeparate : SeparatelyContinuous beta) :
    Continuous beta := by sorry

end QAlgorithms.Papers.Independent.Next46.P25

end
