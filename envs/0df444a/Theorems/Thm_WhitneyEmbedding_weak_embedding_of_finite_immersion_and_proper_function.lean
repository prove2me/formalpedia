-- Prove2me | Theorems.Thm_WhitneyEmbedding_weak_embedding_of_finite_immersion_and_proper_function
-- name    : WhitneyEmbedding.weak_embedding_of_finite_immersion_and_proper_function
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:45:08.121716+00:00
-- url     : https://prove2.me/theorems/e6612873-2029-487a-a512-dde0fbcc3d6b
-- title:
--   Weak Whitney embedding from a finite immersion and a proper smooth function
-- statement:
--   Let $M$ be a Hausdorff, second-countable smooth real $n$-manifold without boundary. Suppose $e:M\to\mathbb R^N$ is a smooth injective immersion and $r:M\to\mathbb R$ is a smooth proper map, meaning that preimages of compact sets are compact. Then $M$ admits a smooth closed embedding into $\mathbb R^{2n+1}$, with injective differential everywhere. All nonnegative dimensions, empty manifolds and disconnected manifolds are allowed. No positivity condition is imposed on $r$.
--
--   This is the weak Whitney construction with its geometric starting data supplied explicitly. It is also valid for noncompact manifolds.
-- source:
--   Zuoqin Wang, Lecture 9: The Whitney Embedding Theorem, Theorem 1.3 (pp.3-4) and proof of Theorem 2.3 (pp.6-7), https://www.math.wustl.edu/~victor/classes/pmf/WhitEmb-Lec09.pdf ; author copy https://staff.ustc.edu.cn/~wangzuoq/Courses/18F-Manifolds/Notes/Lec09.pdf . This is the explicitly conditional construction in that proof: the finite injective immersion and proper smooth function are supplied as hypotheses. Positivity of the proper function is unnecessary because the compact-preimage estimate bounds its absolute value. The bounded diffeomorphism is x/sqrt(1+norm(x)^2), as in Mathlib OpenPartialHomeomorph.univUnitBall; the source PDF p.6 displays x/(1+norm(x)^2), which is not injective as written. The formalization uses the corrected standard smooth compression x/sqrt(1+norm(x)^2). The PDF page was visually checked.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.weak_embedding_of_finite_immersion_and_proper_function (n N : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hei : Injective e) (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x))
    (r : M → ℝ) (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r) (hrp : IsProperMap r) :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ f ∧ IsClosedEmbedding f ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) f x) := by sorry
