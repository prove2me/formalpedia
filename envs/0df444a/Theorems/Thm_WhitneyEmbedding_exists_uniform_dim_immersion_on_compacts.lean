-- Prove2me | Theorems.Thm_WhitneyEmbedding_exists_uniform_dim_immersion_on_compacts
-- name    : WhitneyEmbedding.exists_uniform_dim_immersion_on_compacts
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T15:23:54.966674+00:00
-- url     : https://prove2.me/theorems/eee9e883-5743-482d-89c3-96e4b10caa8c
-- title:
--   Immersions of compact subsets with a uniform target dimension
-- statement:
--   Let $M$ be a Hausdorff, second-countable smooth manifold of dimension $n$. Then there is a single integer $m$, depending only on $M$ (in fact only on $n$), such that **every** compact subset $K \subseteq M$ admits a globally defined smooth map
--   $$g : M \to \mathbb{R}^m$$
--   which is injective on $K$ and whose differential $dg_x$ is injective at every point $x \in K$.
--
--   The point of the statement is the *uniformity* of the target dimension $m$: for a fixed compact set $K$ one obtains such a map with no effort, by covering $K$ with finitely many charts and using a subordinate family of bump functions (this is the construction behind the compact Whitney immersion theorem, `SmoothBumpCovering.exists_immersion_euclidean` in Mathlib), but the number of charts required, and hence the dimension of the target, then grows with $K$. To keep $m$ independent of $K$ one uses that an $n$-manifold admits arbitrarily fine open covers of multiplicity at most $n+1$: the finitely many charts covering $K$ may be organized into at most $n+1$ groups of pairwise disjoint sets, each group contributing $n+1$ coordinates, so that $m = (n+1)^2$ suffices. Alternatively $m = 2n+1$ works, by Whitney's generic projection argument.
--
--   This lemma is the local half of the weak Whitney immersion theorem for noncompact manifolds: it produces immersions on compact pieces of $M$ with target dimension that does not degrade as the pieces exhaust $M$, which is what makes it possible to glue them into a single finite-dimensional injective immersion.
-- source:
--   Zuoqin Wang, Lecture 9: The Whitney Embedding Theorem, Theorem 2.1 and its proof, printed p.5, https://www.math.wustl.edu/~victor/classes/pmf/WhitEmb-Lec09.pdf

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.exists_uniform_dim_immersion_on_compacts (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] :
    ∃ m : ℕ, ∀ K : Set M, IsCompact K →
      ∃ g : M → EuclideanSpace ℝ (Fin m),
        ContMDiff (𝓡 n) (𝓡 m) ∞ g ∧ InjOn g K ∧
        ∀ x ∈ K, Injective (mfderiv (𝓡 n) (𝓡 m) g x) := by sorry
