-- Prove2me | Theorems.Thm_WhitneyEmbedding_smooth_proper_function_of_noncompact
-- name    : WhitneyEmbedding.smooth_proper_function_of_noncompact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T11:42:56.61197+00:00
-- url     : https://prove2.me/theorems/a79c8a23-c4c0-4b39-9fa0-dba935047ee1
-- title:
--   Smooth proper function for a noncompact manifold
-- statement:
--   Let $M$ be a noncompact, Hausdorff, second-countable smooth manifold of dimension $n$. Then there exists a smooth proper function $r : M 	o \mathbb{R}$. Such a function is often called a smooth exhaustion function, meaning its sublevel sets are compact. The existence of such a function is a fundamental property of noncompact paracompact manifolds and provides the essential height data used to embed the manifold into Euclidean space.
-- source:
--   Zuoqin Wang, Lecture 9: The Whitney Embedding Theorem, Theorem 2.1 and its proof, printed p.5, https://www.math.wustl.edu/~victor/classes/pmf/WhitEmb-Lec09.pdf

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.smooth_proper_function_of_noncompact (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (hM : ¬ CompactSpace M) :
    ∃ r : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r ∧ IsProperMap r := by sorry
