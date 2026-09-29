-- Prove2me | Theorems.Thm_WhitneyEmbedding_exists_proper_self_transverse_immersion
-- name    : WhitneyEmbedding.exists_proper_self_transverse_immersion
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T17:17:31.54898+00:00
-- url     : https://prove2.me/theorems/a1c2914a-d59b-4425-8804-cfa83730270c
-- title:
--   General position: a proper self-transverse immersion in $\mathbb{R}^{2n}$
-- statement:
--   Let $n\ge 1$ and let $M$ be a Hausdorff, second-countable smooth real $n$-manifold without boundary. Suppose $e:M\to\mathbb R^{2n+1}$ is a smooth closed embedding whose differential $d e_x$ is injective at every point $x\in M$.
--
--   Then there exists a smooth map
--   $$f:M\longrightarrow\mathbb R^{2n}$$
--   with the following three properties.
--
--   1. $f$ is proper: the preimage of every compact subset of $\mathbb R^{2n}$ is compact.
--   2. $f$ is an immersion: $df_x:T_xM\to\mathbb R^{2n}$ is injective for every $x\in M$.
--   3. $f$ is self-transverse: whenever $x\ne y$ satisfy $f(x)=f(y)$, the two $n$-dimensional tangent planes meet transversally, i.e.
--   $$\operatorname{im}(df_x)+\operatorname{im}(df_y)=\mathbb R^{2n}.$$
--
--   This is the general-position stage in the passage from a closed embedding in $\mathbb R^{2n+1}$ to an embedding in $\mathbb R^{2n}$. It produces a map that already has all the regularity one needs — properness and injective differential — and whose only defect is a set of double points, which by condition 3 are transverse and hence isolated. The subsequent stage of the classical argument removes those double points.
--
--   **Formalization Note** Transversality at a double point is written as the condition that the linear span of the union of the ranges of the two differentials is the whole space; since $\dim M=n$ and the target has dimension $2n$, this is equivalent to the two tangent planes being complementary. Properness is `IsProperMap`, which in Lean also carries continuity of the map.
-- source:
--   H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. of Math. 45 (1944), pp. 220-246. See also MIT 18.965 Lectures 21-22, Theorem 19.1 and Proposition 19.4, pp. 48-51, https://ocw.mit.edu/courses/18-965-geometry-of-manifolds-fall-2004/d0598b3b5ced2d2d0a9884ee14abeae3_lecture21_22.pdf . This is the general-position step preceding Theorem 19.1 there: a closed embedding in R^{2n+1} is followed by a projection and a small perturbation to yield a proper immersion in R^{2n} in general position, whose double points are transverse.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.exists_proper_self_transverse_immersion (n : ℕ) (hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e) (hei : IsClosedEmbedding e)
    (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f ∧ IsProperMap f ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x)) ∧
      (∀ x y, x ≠ y → f x = f y →
        Submodule.span ℝ
          ((Set.range (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) ∪
            Set.range (mfderiv (𝓡 n) (𝓡 (2 * n)) f y) :
              Set (EuclideanSpace ℝ (Fin (2 * n))))) = ⊤) := by sorry
