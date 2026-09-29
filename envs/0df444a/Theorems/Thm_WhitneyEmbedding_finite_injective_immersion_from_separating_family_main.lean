-- Prove2me | Theorems.Thm_WhitneyEmbedding_finite_injective_immersion_from_separating_family_main
-- name    : WhitneyEmbedding.finite_injective_immersion_from_separating_family_main
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T15:03:11.223951+00:00
-- url     : https://prove2.me/theorems/322d316b-0815-4d86-a1b4-020ec6d15552
-- title:
--   Main lemma for finite injective immersion from a separating family
-- statement:
--   Let $M$ be a Hausdorff, second-countable smooth manifold of dimension $n$, and let $\{f_k\}_{k=0}^\infty$ be a sequence of smooth functions with compact support that separate points and tangent vectors. Then there exists an integer $N$ and a choice of $N$ functions from the sequence that form a smooth injective immersion $e : M \to \mathbb{R}^N$. This is a core lemma used in the proof of the Whitney Embedding Theorem.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.finite_injective_immersion_from_separating_family_main (n : ℕ)
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
