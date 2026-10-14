-- Prove2me | Theorems.Thm_WhitneyEmbedding_strong_embedding_from_closed_weak_embedding
-- name    : WhitneyEmbedding.strong_embedding_from_closed_weak_embedding
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:44:58.40738+00:00
-- url     : https://prove2.me/theorems/fd8ef381-293a-4478-9c4b-cf29252eb2ba
-- title:
--   Strong Whitney step from a smooth closed embedding in dimension $2n+1$
-- statement:
--   Let $n\ge1$ and let $M$ be a Hausdorff, second-countable smooth real $n$-manifold without boundary. Assume a smooth closed embedding $e:M\to\mathbb R^{2n+1}$ with injective differential is given. There exists a smooth topological embedding $f:M\to\mathbb R^{2n}$ with injective differential everywhere. Only existence of the resulting embedding is asserted.
--
--   This is the remaining strong Whitney stage. It includes dimensions 1 and 2, all orientability types, disconnected manifolds, and noncompact manifolds. The elementary projection estimate alone does not settle it.
-- source:
--   LeanEval v1, LeanEval/Geometry/WhitneyEmbedding.lean, declaration LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding at commit 296b7491ec989d21bcf8636a9a69231a1e5d1d25, https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/WhitneyEmbedding.lean . This is the strong theorem with the weak closed embedding supplied as additional starting data, isolating the last geometric stage. Historical source: H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. Math.45 (1944), pp.220-246. MIT 18.965 Lectures21-22, Theorem19.1 and Proposition19.4, pp.48-51, https://ocw.mit.edu/courses/18-965-geometry-of-manifolds-fall-2004/d0598b3b5ced2d2d0a9884ee14abeae3_lecture21_22.pdf gives the compact high-dimensional mechanism; that lecture alone does not cover all the low-dimensional and noncompact cases required here.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.strong_embedding_from_closed_weak_embedding (n : ℕ) (hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e) (hei : IsClosedEmbedding e)
    (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f ∧ IsEmbedding f ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) := by sorry
