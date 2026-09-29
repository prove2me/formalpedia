-- Prove2me | Theorems.Thm_WhitneyEmbedding_exists_separating_smooth_functions
-- name    : WhitneyEmbedding.exists_separating_smooth_functions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T11:59:39.654979+00:00
-- url     : https://prove2.me/theorems/1d1c7abb-ba91-4073-9a5e-2a3e8d5070ab
-- title:
--   Existence of a countable separating family of smooth functions
-- statement:
--   Let $M$ be a Hausdorff, second-countable smooth manifold of dimension $n$. Then there exists a countable sequence of smooth functions $f_k : M \to \mathbb{R}$ with compact support such that the family $\{f_k\}$ separates points and separates tangent vectors.
--
--   Specifically, for any two distinct points $x, y \in M$, there exists some $k$ such that $f_k(x) \neq f_k(y)$. Furthermore, for any point $x \in M$ and any non-zero tangent vector $v \in T_x M$, there exists some $k$ such that the differential $df_k(x)$ evaluated on $v$ is non-zero. This family is constructed using a smooth partition of unity subordinate to a countable, locally finite cover of $M$ by precompact coordinate charts.
-- source:
--   Standard construction in differential topology using partitions of unity. See, for example, Lee, Introduction to Smooth Manifolds, Theorem 6.14.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.exists_separating_smooth_functions (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] :
    ∃ (seq : ℕ → M → ℝ),
      (∀ k, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (seq k)) ∧
      (∀ k, HasCompactSupport (seq k)) ∧
      (∀ x y, x ≠ y → ∃ k, seq k x ≠ seq k y) ∧
      (∀ x, ∀ (v : TangentSpace (𝓡 n) x), v ≠ 0 → ∃ k, mfderiv (𝓡 n) 𝓘(ℝ) (seq k) x v ≠ 0) := by sorry
