-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_subdifferential_nonempty_bounded_convex_closed
-- name    : ShorNonsmooth.Subdiff.subdifferential_nonempty_bounded_convex_closed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:14:32.517864+00:00
-- url     : https://prove2.me/theorems/1003eeca-db2d-46cc-9d66-96d55a82f43d
-- title:
--   Theorem 1.7 — the subdifferential at an interior point is nonempty, bounded, convex and closed
-- statement:
--   Let $M \subseteq E_n$ and let $f$ be convex on $M$. Let $x_0$ be an interior point of $M$ and let $G(x_0)$ be the subdifferential of $f$ at $x_0$, the set of $g$ with $f(x) - f(x_0) \ge (g, x - x_0)$ for all $x \in M$. Then
--
--   $$
--   G(x_0) \neq \emptyset, \qquad G(x_0) \text{ is bounded, convex and closed.}
--   $$
--
--   In particular $G(x_0)$ is a nonempty compact convex set, which is what makes maxima over it (as in the max formula for directional derivatives) attained.
--
--   **Formalization Note** "Bounded" is `Bornology.IsBounded`; convexity of $f$ on $M$ is `ConvexOn ℝ M f`, which includes convexity of $M$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, Theorem 1.7

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 9, Theorem 1.7: the subdifferential `G(x₀)` of a convex function `f` with
domain `M` at an interior point `x₀` of `M` is nonempty, bounded, convex and closed. -/
theorem subdifferential_nonempty_bounded_convex_closed {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ M f) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    (subdifferential M f x₀).Nonempty ∧ Bornology.IsBounded (subdifferential M f x₀) ∧
      Convex ℝ (subdifferential M f x₀) ∧ IsClosed (subdifferential M f x₀) := by sorry

end ShorNonsmooth.Subdiff
