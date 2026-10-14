-- Prove2me | Theorems.Thm_WhitneyEmbedding_finite_immersion_and_proper_function_of_noncompact
-- name    : WhitneyEmbedding.finite_immersion_and_proper_function_of_noncompact
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:44:51.479933+00:00
-- url     : https://prove2.me/theorems/989aea68-4ad7-43c8-b32f-b30c205107f5
-- title:
--   Finite-dimensional immersion and smooth exhaustion data for a noncompact manifold
-- statement:
--   Every noncompact Hausdorff, second-countable smooth real $n$-manifold without boundary has a smooth injective immersion $e:M\to\mathbb R^N$ for some finite $N$, and a smooth proper function $r:M\to\mathbb R$. The differential of $e$ is injective at every point. No connectedness or positive-dimensional hypothesis is required; properness has its ordinary topological meaning that compact sets have compact preimages.
--
--   These are the starting data needed by the noncompact weak Whitney construction. Their existence remains an open dependency in the formal development.
-- source:
--   Zuoqin Wang, Lecture 9: The Whitney Embedding Theorem, Theorem 2.1 and its proof, printed p.5, https://www.math.wustl.edu/~victor/classes/pmf/WhitEmb-Lec09.pdf . Its opening step invokes a positive smooth exhaustion, and its construction produces an injective immersion in R^(4n+3); the present statement retains existence of some finite ambient dimension and records the proper function already used there. Positivity is omitted as unnecessary. The formal n=0 extension follows by assigning proper heights to a countable discrete manifold.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.finite_immersion_and_proper_function_of_noncompact (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (hM : ¬ CompactSpace M) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)) (r : M → ℝ),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) ∧
      ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r ∧ IsProperMap r := by sorry
