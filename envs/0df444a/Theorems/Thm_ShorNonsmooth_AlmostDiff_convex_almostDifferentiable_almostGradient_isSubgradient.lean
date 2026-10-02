-- Prove2me | Theorems.Thm_ShorNonsmooth_AlmostDiff_convex_almostDifferentiable_almostGradient_isSubgradient
-- name    : ShorNonsmooth.AlmostDiff.convex_almostDifferentiable_almostGradient_isSubgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:58:52.597387+00:00
-- url     : https://prove2.me/theorems/01b1746b-7f29-4822-aa26-83171e8c470c
-- title:
--   Theorem 1.15 — convex functions are almost differentiable and their almost-gradients are subgradients
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex. Then
--
--   1. $f$ is almost differentiable: it is Lipschitz on every bounded set, differentiable almost everywhere, and its gradient is continuous on the set of points where it is differentiable;
--   2. at every point $x_0 \in E_n$, every almost-gradient of $f$ is a subgradient:
--
--   $$
--   G(x_0) \subseteq G_f(x_0) = \{ g \in E_n : f(x) - f(x_0) \ge (g, x - x_0) \ \text{for all } x \in E_n \}.
--   $$
--
--   The theorem places convex functions inside the class of almost differentiable functions, so that methods designed for almost-gradients apply to convex minimization, with every almost-gradient a valid subgradient.
--
--   **Formalization Note** The printed theorem says that the almost-gradients "coincide with" the subgradients. That set equality is false: for $f(x) = |x|$ on $E_1$ the almost-gradients at $0$ are $\{-1, 1\}$, while the subgradients form $[-1, 1]$. The book's proof establishes exactly the inclusion stated here, and this is what is formalized. (The true equality is between the subdifferential and the closed convex hull of the almost-gradients; the book does not prove it.)
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 18, Theorem 1.15 (corrected: inclusion, as proved)

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, Theorem 1.15, in the form its proof establishes: a convex function `f`
on `E_n` is almost differentiable, and at every point `x₀` every almost-gradient of `f` is a
subgradient of `f` at `x₀`.

The printed statement says the almost-gradients "coincide with" the subgradients; that set
equality is false (for `f(x) = |x|` on `ℝ¹` the almost-gradients at `0` are `{-1, 1}` while the
subgradients form `[-1, 1]`), and the book's proof shows only the inclusion stated here. -/
theorem convex_almostDifferentiable_almostGradient_isSubgradient {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    AlmostDifferentiable f ∧
      ∀ x₀ : EuclideanSpace ℝ (Fin n), ∀ g ∈ almostGradients f x₀,
        IsSubgradient f x₀ g := by sorry

end ShorNonsmooth.AlmostDiff
