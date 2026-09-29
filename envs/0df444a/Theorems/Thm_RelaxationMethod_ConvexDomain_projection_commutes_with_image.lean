-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_projection_commutes_with_image
-- name    : RelaxationMethod.ConvexDomain.projection_commutes_with_image
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:52:44.73024+00:00
-- url     : https://prove2.me/theorems/e507e5bc-2297-4fdd-9b3e-63f56f6850a9
-- title:
--   §10 — orthogonal projection on a flat containing $A$ commutes with the image map
-- statement:
--   Let $A \subseteq E_n$ be a nonempty closed bounded convex set contained in a flat $L$, and let $\pi$ be the orthogonal projection of $E_n$ on $L$. For all points $p, p_1 \in E_n$:
--
--   1. a point $q \in A$ is nearest to $p$ among the points of $A$ if and only if it is nearest to $\pi(p)$;
--   2. if $p_1$ is an image of $p$ with respect to $A$, then $\pi(p_1)$ is an image of $\pi(p)$ with respect to $A$, i.e. $p'_1 = F(p'_0)$ for the projections $p'_0 = \pi(p)$, $p'_1 = \pi(p_1)$; moreover
--   $$p_1 - \pi(p_1) = -\bigl(p - \pi(p)\bigr), \qquad \operatorname{dist}(p_1, L) = \operatorname{dist}(p, L),$$
--   so $p_1$ lies at the same distance from $L$ as $p$, on the opposite side.
--
--   This is the reduction of Theorem 3, Case 2 to Case 1.
--
--   **Formalization Note** The paper first reduces to $r = n - 1$ and projects on the hyperplane $L_{n-1}$; we state the claims for any flat $L \supseteq A$, which covers $L = L_r$ directly. When $\pi(p) \in A$ the image of $\pi(p)$ is $\pi(p)$ itself, which is the paper's "terminates with a first $p'_N \in A$".
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 404, §10, proof of Theorem 3, Case 2

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess

namespace RelaxationMethod.ConvexDomain

/-- §10, p. 404: let `A` lie in the flat `L` and let `π` be the orthogonal projection on `L`.
(i) A point `q ∈ A` is nearest to `p` iff it is nearest to `π p`.
(ii) If `p₁ = F(p)` then `π p₁ = F(π p)` (in the relational sense of `IsImage`, which at a point
of `A` returns the point itself), `p₁` lies on the other side of `L` from `p`
(`p₁ - π p₁ = -(p - π p)`), and `dist (p₁, L) = dist (p, L)`. -/
theorem projection_commutes_with_image {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L] (hAL : A ⊆ L)
    (p p₁ : EuclideanSpace ℝ (Fin n)) :
    (∀ q ∈ A, ((∀ a ∈ A, dist p q ≤ dist p a) ↔
      (∀ a ∈ A, dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) q ≤
        dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) a))) ∧
    (IsImage A p p₁ →
      IsImage A (EuclideanGeometry.orthogonalProjection L p)
          (EuclideanGeometry.orthogonalProjection L p₁) ∧
        p₁ - (EuclideanGeometry.orthogonalProjection L p₁ : EuclideanSpace ℝ (Fin n)) =
          -(p - (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n))) ∧
        Metric.infDist p₁ (L : Set (EuclideanSpace ℝ (Fin n))) =
          Metric.infDist p (L : Set (EuclideanSpace ℝ (Fin n)))) := by sorry

end RelaxationMethod.ConvexDomain
