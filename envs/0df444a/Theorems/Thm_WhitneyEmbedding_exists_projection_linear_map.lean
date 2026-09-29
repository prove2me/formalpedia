-- Prove2me | Theorems.Thm_WhitneyEmbedding_exists_projection_linear_map
-- name    : WhitneyEmbedding.exists_projection_linear_map
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-11T11:49:29.176188+00:00
-- url     : https://prove2.me/theorems/5fc6e124-5222-49a4-938d-63f6c329ef1b
-- title:
--   Existence of a projection linear map for dimension reduction
-- statement:
--   Let $M$ be a Hausdorff, second-countable smooth manifold of dimension $n \ge 1$, and let $e : M 	o \mathbb{R}^{2n+1}$ be a smooth closed embedding with injective differential. Then there exists a surjective continuous linear map $L : \mathbb{R}^{2n+1} 	o \mathbb{R}^{2n}$ such that the composition $f = L \circ e : M 	o \mathbb{R}^{2n}$ is a smooth proper injective map with injective differential everywhere.
--
--   This lemma encapsulates the core geometric argument of the strong Whitney embedding theorem. By analyzing the secant and tangent varieties of the embedded manifold $e(M)$ in $\mathbb{R}^{2n+1}$, one can show that these varieties have dimension at most $2n$. Using Sard's theorem or a Baire category argument on the projective space $\mathbb{P}^{2n}$, one finds a generic projection direction that avoids both the secant variety (ensuring injectivity) and the tangent variety (ensuring immersion). Because $e$ is a closed embedding (hence proper), choosing a projection direction that also avoids the asymptotic cone of $e(M)$ guarantees that the resulting map $f$ remains proper.
-- source:
--   H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. Math. 45 (1944), pp.220-246.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.exists_projection_linear_map (n : ℕ) (hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e) (hei : IsClosedEmbedding e)
    (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) :
    ∃ (L : EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))),
      Function.Surjective L ∧
      let f := L ∘ e
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f ∧ Injective f ∧ IsProperMap f ∧ 
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) := by sorry
