-- Prove2me | Theorems.Thm_WhitneyEmbedding_strong_embedding_low_dimensions
-- name    : WhitneyEmbedding.strong_embedding_low_dimensions
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T17:17:31.712972+00:00
-- url     : https://prove2.me/theorems/87a29d90-e727-4e18-88ed-5b5d3ffb41d1
-- title:
--   Strong Whitney embedding in dimensions $n \le 2$
-- statement:
--   Let $n\in\{1,2\}$ and let $M$ be a Hausdorff, second-countable smooth real $n$-manifold without boundary that admits a smooth closed embedding $e:M\to\mathbb R^{2n+1}$ with injective differential. Then there exists a smooth topological embedding
--   $$f:M\longrightarrow\mathbb R^{2n}$$
--   whose differential $df_x$ is injective at every point.
--
--   Concretely this asserts two classical facts: every smooth $1$-manifold (a countable disjoint union of copies of $\mathbb R$ and of circles) embeds smoothly in the plane, and every smooth surface, compact or not, orientable or not, embeds smoothly in $\mathbb R^4$.
--
--   These are the two dimensions that the Whitney trick does not reach: the cancellation of a pair of transverse double points requires an embedded Whitney disc, which needs $2n\ge6$. Both low-dimensional cases are true and are handled by arguments specific to dimensions $1$ and $2$.
--
--   **Formalization Note** The hypotheses are stated exactly as in the parent theorem, with the extra bounds $1\le n$ and $n\le 2$, so that the statement can be used verbatim in the case split of the general theorem. The closed embedding $e$ into $\mathbb R^{2n+1}$ is supplied as data even though the classical low-dimensional arguments do not need it.
-- source:
--   Dimension 1: classification of smooth 1-manifolds, J. Milnor, Topology from the Differentiable Viewpoint, Appendix, pp. 55-57. Dimension 2: H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. of Math. 45 (1944), pp. 220-246; see also M. Hirsch, Differential Topology, Springer GTM 33, Chapter 2. These are the cases n = 1, 2 of the strong Whitney embedding theorem, excluded from the Whitney trick, which needs 2n >= 6.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.strong_embedding_low_dimensions (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≤ 2)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e) (hei : IsClosedEmbedding e)
    (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f ∧ IsEmbedding f ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) := by sorry
