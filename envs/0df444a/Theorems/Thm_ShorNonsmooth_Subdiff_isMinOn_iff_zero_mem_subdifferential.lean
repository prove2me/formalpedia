-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_isMinOn_iff_zero_mem_subdifferential
-- name    : ShorNonsmooth.Subdiff.isMinOn_iff_zero_mem_subdifferential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:22:20.769036+00:00
-- url     : https://prove2.me/theorems/97edc554-8e06-41b3-b44b-449bdc657150
-- title:
--   Corollary (p. 12) — $x_0$ minimizes $f$ on $M$ iff $0 \in G(x_0)$
-- statement:
--   Let $M \subseteq E_n$, let $f$ be convex on $M$, and let $x_0$ be an interior point of $M$. Then $x_0$ is a point of the minimum of $f$ on $M$ if and only if the zero vector is a subgradient:
--
--   $$
--   f(x_0) \le f(x) \ \text{ for all } x \in M \iff 0 \in G(x_0).
--   $$
--
--   This is the optimality condition of nonsmooth convex minimization.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 12, Corollary (after Theorem 1.11)

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 12, Corollary (to Theorem 1.11): for a convex function `f` with domain `M`
and an interior point `x₀` of `M`, `x₀` is a point of the minimum of `f` on `M` if and only if
`0 ∈ G(x₀)`. -/
theorem isMinOn_iff_zero_mem_subdifferential {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ M f) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    (∀ x ∈ M, f x₀ ≤ f x) ↔ (0 : EuclideanSpace ℝ (Fin n)) ∈ subdifferential M f x₀ := by sorry

end ShorNonsmooth.Subdiff
