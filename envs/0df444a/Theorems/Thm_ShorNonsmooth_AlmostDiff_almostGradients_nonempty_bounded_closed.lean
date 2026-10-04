-- Prove2me | Theorems.Thm_ShorNonsmooth_AlmostDiff_almostGradients_nonempty_bounded_closed
-- name    : ShorNonsmooth.AlmostDiff.almostGradients_nonempty_bounded_closed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:57:37.381006+00:00
-- url     : https://prove2.me/theorems/e6c2d262-70da-434a-a959-b886ff47e97e
-- title:
--   Theorem 1.14 — the set of almost-gradients is nonempty, bounded and closed
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be almost differentiable, and write $G(x)$ for the set of almost-gradients of $f$ at $x$. Then for every $x \in E_n$
--
--   $$
--   G(x) \neq \emptyset, \qquad G(x) \text{ is bounded}, \qquad G(x) \text{ is closed}.
--   $$
--
--   This makes $G(x)$ (and its closed convex hull, the set of generalized almost-gradients) a compact set that can play the role of the gradient in descent methods for almost differentiable functions.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 18, Theorem 1.14

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, Theorem 1.14: for an almost differentiable `f` on `E_n`, the set `G(x)`
of almost-gradients is nonempty, bounded and closed at every point `x`. -/
theorem almostGradients_nonempty_bounded_closed {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AlmostDifferentiable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    (almostGradients f x).Nonempty ∧ Bornology.IsBounded (almostGradients f x) ∧
      IsClosed (almostGradients f x) := by sorry

end ShorNonsmooth.AlmostDiff
