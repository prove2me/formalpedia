-- Prove2me | Theorems.Thm_ShorNonsmooth_Ellipsoid_dilation_norm_eq
-- name    : ShorNonsmooth.Ellipsoid.dilation_norm_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:17:17.656985+00:00
-- url     : https://prove2.me/theorems/459fdf5f-821a-410f-a001-58f3f804bdd7
-- title:
--   Eq. (3.4) — the norm of a vector after space dilation along $\xi$
-- statement:
--   Let $\xi \in E_n$ be a unit vector, $\alpha$ a real number, and $R_\alpha(\xi) = I + (\alpha - 1)\xi\xi^T$ the operator of space dilation along $\xi$ with coefficient $\alpha$. Then for every $x \in E_n$,
--   $$
--   \|R_\alpha(\xi)\,x\| = \sqrt{\|x\|^2 + (\alpha^2 - 1)(x, \xi)^2}.
--   $$
--
--   The identity measures how a dilation changes lengths: only the component of $x$ along $\xi$ is rescaled. It is the computation behind the induction step of Theorem 3.14.
--
--   **Formalization Note** The book fixes $\alpha \ge 0$ at the start of §3.2; the identity holds for every real $\alpha$, and the Lean statement does not assume $\alpha \ge 0$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 50, property 9), Eq. (3.4)

import Mathlib
import Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), p. 50, property 9), formula (3.4): for a unit vector `ξ` and every `x ∈ E_n`,
`‖R_α(ξ) x‖ = √(‖x‖² + (α² - 1)(x, ξ)²)`. The identity holds for every real `α`
(the section fixes `α ≥ 0`; the hypothesis is not needed and is dropped). -/
theorem dilation_norm_eq {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin (dilationMatrix α ξ) x‖ =
      Real.sqrt (‖x‖ ^ 2 + (α ^ 2 - 1) * (inner ℝ x ξ) ^ 2) := by sorry

end ShorNonsmooth.Ellipsoid
