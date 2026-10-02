-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_norm_eq
-- name    : ShorNonsmooth.SpaceDilation.dilation_norm_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:05:44.892341+00:00
-- url     : https://prove2.me/theorems/f16f76a5-433b-44bd-95a2-7e0038530bb7
-- title:
--   Eq. (3.4) — the norm of a dilated vector
-- statement:
--   Let $\xi \in E_n$ be a unit vector, $\alpha \ge 0$, and let $R_\alpha(\xi)$ be the operator of space dilation along $\xi$ with coefficient $\alpha$, $R_\alpha(\xi)x = x + (\alpha - 1)(x,\xi)\,\xi$. Then for every $x \in E_n$
--   $$
--   \|R_\alpha(\xi)\,x\| = \sqrt{\|x\|^2 + (\alpha^2 - 1)(x, \xi)^2} .
--   $$
--
--   This identity measures how much a single dilation lengthens a vector, and is the basic estimate in the convergence proofs of the SDG method (Theorems 3.2 and 3.3).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 50, property 9), formula (3.4)

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), p. 50, property 9), formula (3.4): for a unit vector `ξ`, a coefficient `α ≥ 0`
and any `x ∈ E_n`, `‖R_α(ξ) x‖ = √(‖x‖² + (α² - 1)(x, ξ)²)`. -/
theorem dilation_norm_eq {n : ℕ} (α : ℝ) (hα : 0 ≤ α) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖dilation α ξ x‖ = Real.sqrt (‖x‖ ^ 2 + (α ^ 2 - 1) * (inner ℝ x ξ) ^ 2) := by sorry

end ShorNonsmooth.SpaceDilation
