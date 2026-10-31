-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P33_regularManifold_product_embedding
-- name    : QAlgorithms.Papers.Independent.Intake100.P33.regularManifold_product_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:57:24.055294+00:00
-- url     : https://prove2.me/theorems/13b03789-0a6a-4b15-8e3b-e0043c0d9998
-- title:
--   Regular locally convex manifolds embed into a point-indexed product
-- statement:
--   Let $r$ be a positive integer or $\infty$. Let $E$ be a Hausdorff real locally convex topological vector space, and let $M$ be a Hausdorff $C^r$ manifold without boundary modelled on $E$, with its maximal compatible atlas. Assume that $M$ is $C^r$-regular: its topology is initial with respect to its real-valued $C^r$ functions. Equivalently, every point and neighbourhood admit a $C^r$ function with values in $[0,1]$, supported in that neighbourhood and equal to one near the point.
--
--   Give $(E\times\mathbb R)^M$, indexed by the full point set of $M$, the product topology and its canonical locally convex vector-space manifold structure. Then
--
--   $$
--   \exists\,\theta:M\longrightarrow(E\times\mathbb R)^M\quad\text{such that }\theta\text{ is a }C^r\text{-embedding}.
--   $$
--
--   Here an embedding is a topological embedding and an immersion: in compatible local charts it is a continuous linear topological embedding onto a complemented subspace. No normability, completeness, countability or paracompactness is assumed. This embeds regular locally convex manifolds in a product of copies of their model space with one additional real coordinate per point.
--
--   **Formalization Note** Finite orders and smooth order are represented by `WithTop ℕ`, with the explicit bound $1\le r$. The top element denotes smoothness, and there is no analytic order. The bump-function characterization stated on source p. 9 is used for regularity. A continuous linear left inverse represents the complemented linear embedding in each local normal form.
-- source:
--   Fundamentals of submersions and immersions between infinite-dimensional manifolds, arXiv:1502.05795v4, PDF p. 9, Theorem J

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P33

namespace QAlgorithms.Papers.Independent.Intake100.P33

open Set Filter Topology

universe u v w z

/-- Theorem J, PDF p. 9; proof PDF pp. 33–34. A C^r-regular real
locally convex C^r manifold embeds in the product indexed by its entire
point set. Positive finite orders and smooth order are allowed; analytic
order is not present. The target carries the product topology and the
canonical vector-space manifold structure. -/
theorem regularManifold_product_embedding
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {M : Type v} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    (r : WithTop ℕ) (hr : (1 : WithTop ℕ) ≤ r)
    (hAtlas : MaximalRealCrAtlas (E := E) (M := M) r)
    (hRegular : RealCrRegular (E := E) (M := M) r) :
    ∃ theta : M → (M → E × ℝ),
      RealCrEmbedding (E := E) (F := M → E × ℝ) r theta := by sorry

end QAlgorithms.Papers.Independent.Intake100.P33
