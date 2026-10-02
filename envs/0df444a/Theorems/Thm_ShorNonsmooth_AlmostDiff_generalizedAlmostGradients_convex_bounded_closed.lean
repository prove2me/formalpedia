-- Prove2me | Theorems.Thm_ShorNonsmooth_AlmostDiff_generalizedAlmostGradients_convex_bounded_closed
-- name    : ShorNonsmooth.AlmostDiff.generalizedAlmostGradients_convex_bounded_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:58:18.725983+00:00
-- url     : https://prove2.me/theorems/cd784f8c-816b-4993-9d98-3b2647d17d60
-- title:
--   p. 19 — the set of generalized almost-gradients is convex, bounded and closed
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be almost differentiable and $x \in E_n$. A **generalized almost-gradient** of $f$ at $x$ is any vector in the closure of the convex hull of the set $G(x)$ of almost-gradients. The set of generalized almost-gradients,
--
--   $$
--   \overline{\operatorname{conv}}\, G(x) = \overline{\operatorname{conv}\, G(x)},
--   $$
--
--   is convex, bounded and closed.
--
--   The book states this as a consequence of Theorem 1.14; it is the analogue, for almost differentiable functions, of the compactness and convexity of the subdifferential of a convex function.
--
--   **Formalization Note** The set of generalized almost-gradients is written inline as `closure (convexHull ℝ (almostGradients f x))`, exactly the book's definition.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 19, Definition (generalized almost-gradient) and the sentence following it

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 19, Definition and the sentence following it: the set of **generalized
almost-gradients** of `f` at `x`, the closure of the convex hull of `G(x)`, is convex, bounded and
closed when `f` is almost differentiable. -/
theorem generalizedAlmostGradients_convex_bounded_closed {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AlmostDifferentiable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ (closure (convexHull ℝ (almostGradients f x))) ∧
      Bornology.IsBounded (closure (convexHull ℝ (almostGradients f x))) ∧
      IsClosed (closure (convexHull ℝ (almostGradients f x))) := by sorry

end ShorNonsmooth.AlmostDiff
