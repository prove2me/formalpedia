-- Prove2me | Theorems.Thm_WhitneyEmbedding_finite_injective_immersion
-- name    : WhitneyEmbedding.finite_injective_immersion
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T11:42:58.278647+00:00
-- url     : https://prove2.me/theorems/436df304-f4fd-4429-a901-029af1604963
-- title:
--   Finite-dimensional injective immersion for a noncompact manifold
-- statement:
--   Let $M$ be a noncompact, Hausdorff, second-countable smooth manifold of dimension $n$. Then there exists a finite integer $N$ and a smooth injective immersion $e : M 	o \mathbb{R}^N$. An immersion is a smooth map whose differential is injective at every point. The existence of a finite-dimensional injective immersion is the core step in the weak Whitney embedding theorem for noncompact manifolds, reducing the infinite-dimensional space of smooth functions to a finite-dimensional Euclidean space via generic linear combinations of a countable partition of unity.
-- source:
--   Zuoqin Wang, Lecture 9: The Whitney Embedding Theorem, Theorem 2.1 and its proof, printed p.5, https://www.math.wustl.edu/~victor/classes/pmf/WhitEmb-Lec09.pdf

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.finite_injective_immersion (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (hM : ¬ CompactSpace M) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by sorry
