-- Prove2me | Theorems.Thm_WhitneyEmbedding_finite_injective_immersion_from_separating_family
-- name    : WhitneyEmbedding.finite_injective_immersion_from_separating_family
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T11:59:26.873787+00:00
-- url     : https://prove2.me/theorems/a879ae4a-3076-46aa-8b8e-a927cba6d74e
-- title:
--   Finite injective immersion from a separating family
-- statement:
--   Let $M$ be a Hausdorff, second-countable smooth manifold of dimension $n$, and let $\{f_k\}_{k=0}^\infty$ be a countable sequence of smooth functions with compact support that separate points and separate tangent vectors. Then there exists a finite integer $N$ and a choice of $N$ functions from the sequence (possibly repeated or linearly combined) that form a smooth injective immersion $e : M \to \mathbb{R}^N$.
--
--   The proof relies on a Baire category argument or a transversality argument. One considers the infinite-dimensional map $F : M \to \mathbb{R}^\infty$ given by $F(x) = (f_0(x), f_1(x), \dots)$. Since the functions separate points and tangent vectors, $F$ is an injective immersion. Because the functions have compact support and $M$ is second-countable, one can show that for a generic finite-dimensional projection $\pi : \mathbb{R}^\infty \to \mathbb{R}^N$, the composition $\pi \circ F$ remains an injective immersion, provided $N$ is sufficiently large (e.g., $N \ge 2n+1$).
-- source:
--   H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. Math. 45 (1944), pp.220-246.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.finite_injective_immersion_from_separating_family (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (seq : ℕ → M → ℝ)
    (hseq_diff : ∀ k, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (seq k))
    (hseq_comp : ∀ k, HasCompactSupport (seq k))
    (hseq_sep : ∀ x y, x ≠ y → ∃ k, seq k x ≠ seq k y)
    (hseq_tan : ∀ x, ∀ (v : TangentSpace (𝓡 n) x), v ≠ 0 → ∃ k, mfderiv (𝓡 n) 𝓘(ℝ) (seq k) x v ≠ 0) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by sorry
