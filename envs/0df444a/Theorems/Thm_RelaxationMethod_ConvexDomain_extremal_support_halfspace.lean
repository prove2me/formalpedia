-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_extremal_support_halfspace
-- name    : RelaxationMethod.ConvexDomain.extremal_support_halfspace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:47:21.413846+00:00
-- url     : https://prove2.me/theorems/c8b2cee6-1431-4459-be99-e19d9ccfe8c2
-- title:
--   §9 — the half-space through the nearest point is the farthest supporting half-space
-- statement:
--   Let $A \subseteq E_n$ be a nonempty closed bounded convex set, let $p \notin A$ and let $q$ be the point of $A$ nearest to $p$. Let $H_0$ be the closed half-space bounded by the hyperplane $\pi_0$ through $q$ normal to the segment $pq$, on the side not containing $p$:
--   $$H_0 = \{x : \langle q - p, x\rangle \ge \langle q - p, q\rangle\}.$$
--   Then
--
--   1. $H_0$ belongs to the family $F$ of supporting half-spaces of $A$;
--   2. $p \notin H_0$ and $\operatorname{dist}(p, H_0) = |p - q|$;
--   3. $\displaystyle \operatorname{dist}(p, H_0) = \max_{H \in F} \operatorname{dist}(p, H)$;
--   4. for every $H \in F$ attaining this maximum and every point $q'$ of $H$ nearest to $p$, $p + 2(q' - p) = p + 2(q - p)$.
--
--   Thus the reflexion process with respect to the infinite family $F$ (the relaxation step with $\lambda = 2$ applied to a farthest half-space) amounts to the construction $p_1 = p + 2(q - p)$ of (3.1).
--
--   **Formalization Note** Item 4 is how we state the paper's "this shows that the reflexion process with respect to the family $F$ amounts to the construction of the point (3.1)": whichever farthest half-space is chosen, the reflexion step gives the same point. Distances to sets are `Metric.infDist`.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 402, §9

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_ConvexDomain_SupportHalfSpace

namespace RelaxationMethod.ConvexDomain

/-- §9, p. 402: for `p ∉ A` with nearest point `q`, the half-space `H₀` bounded by the hyperplane
through `q` normal to `pq` and not containing `p` belongs to `F`, has distance `|p - q|` from `p`,
maximizes the distance from `p` over `F`, and the reflexion step with respect to any maximizing
`H ∈ F` produces `p + 2(q - p)`. -/
theorem extremal_support_halfspace {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p q : EuclideanSpace ℝ (Fin n)) (hp : p ∉ A) (hq : IsNearestPoint A p q)
    (H₀ : Set (EuclideanSpace ℝ (Fin n)))
    (hH₀ : H₀ = {x | inner ℝ (q - p) q ≤ inner ℝ (q - p) x}) :
    IsSupportHalfSpace A H₀ ∧ p ∉ H₀ ∧ Metric.infDist p H₀ = dist p q ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H ≤ Metric.infDist p H₀) ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H = Metric.infDist p H₀ →
        ∀ q' ∈ H, dist p q' = Metric.infDist p H →
          p + (2 : ℝ) • (q' - p) = p + (2 : ℝ) • (q - p)) := by sorry

end RelaxationMethod.ConvexDomain
