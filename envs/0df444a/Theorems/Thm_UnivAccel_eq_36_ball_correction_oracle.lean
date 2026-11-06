-- Prove2me | Theorems.Thm_UnivAccel_eq_36_ball_correction_oracle
-- name    : UnivAccel.eq_36_ball_correction_oracle
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:42.933208+00:00
-- url     : https://prove2.me/theorems/8408e3d5-84fb-4601-b4cc-f61ea5ee5c06
-- title:
--   Eq. (36) — the ball oracle is a correction oracle with $p = x_c$, $\lambda = \|\nabla f(x_c)\|/r$
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$, let $r > 0$, and let $x_c = \mathrm{Ball}^f_r(x_p)$ be a minimizer of $f$ over the closed ball of radius $r$ around $x_p$. Set $\lambda = \|\nabla f(x_c)\|/r$. Then
--   1. $(x_c, \lambda)$ is a valid answer of a correction oracle (Definition 1) at $x_p$, and (25) holds with $p = x_c$:
--   $$
--   \lambda(x_p - x_c) = \nabla f(x_c) + \mu(x_c - x_c);
--   $$
--   2. if $\nabla f(x_c) \neq 0$, the ball constraint is active, $\|x_p - x_c\| = r$, and $\nabla f(x_c) = \lambda(x_p - x_c)$;
--   3. if $\nabla f(x_c) = 0$, then $x_c$ minimizes $f$ and $\lambda = 0$.
--
--   This identifies the ball oracle as the implicit ($p = u$) instance of the correction oracle, which is what lets the general lookahead step (27) run with ball queries.
--
--   Differences from the source: none.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.3, eq. (36) with (25), p.21

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_IsCorrectionOutput

namespace UnivAccel

/-- §5.3, eq. (36) with (25), p.21 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)). Let `f` be differentiable and `μ`-strongly convex
(`μ > 0`), `r > 0`, and let `x_c` be a minimizer of `f` over the closed ball of radius `r` around
`x_p` (`x_c = Ball^f_r(x_p)`). With `λ = ‖∇f(x_c)‖/r`, the pair `(x_c, λ)` is a valid answer of a
correction oracle (Definition 1) at `x_p`, and (25) holds with `p = x_c`; if `∇f(x_c) ≠ 0` the ball
constraint is active and `∇f(x_c) = λ(x_p − x_c)`; if `∇f(x_c) = 0`, then `x_c` minimizes `f` and
`λ = 0`. -/
theorem eq_36_ball_correction_oracle {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r : ℝ)
    (xp xc : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ) (hr : 0 < r)
    (hxc : IsBallMin f xp r xc) :
    IsCorrectionOutput f μ xp xc (‖gradient f xc‖ / r) ∧
    (‖gradient f xc‖ / r) • (xp - xc) = gradient f xc + μ • (xc - xc) ∧
    (gradient f xc ≠ 0 →
      ‖xp - xc‖ = r ∧ gradient f xc = (‖gradient f xc‖ / r) • (xp - xc)) ∧
    (gradient f xc = 0 → (∀ y, f xc ≤ f y) ∧ ‖gradient f xc‖ / r = 0) := by sorry

end UnivAccel
