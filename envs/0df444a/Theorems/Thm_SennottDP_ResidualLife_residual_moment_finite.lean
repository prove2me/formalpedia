-- Prove2me | Theorems.Thm_SennottDP_ResidualLife_residual_moment_finite
-- name    : SennottDP.ResidualLife.residual_moment_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T10:28:33.615987+00:00
-- url     : https://prove2.me/theorems/87cf2813-1163-4c60-8bad-37da9994da95
-- title:
--   Proposition 9.2.3 — a finite k-th moment of Y gives finite k-th moments of every residual life Y_s
-- statement:
--   Let $Y$ take values in $\{1,2,\dots\}$ with tail $F^*(y) = P(Y>y)$, and for $s \ge 0$ with $F^*(s) > 0$ let $Y_s$ be the residual life, $P(Y_s = y) = u_{s+y}/F^*(s)$ for $y \ge 1$. Fix a positive integer $k$. If $E[Y^k] < \infty$, then
--   $$E[Y_s^k] < \infty \qquad \text{for all } s \ge 0 \text{ with } F^*(s) > 0.$$
--
--   Finiteness of a moment of the service time is thus inherited by the remaining service time at every stage of an uncompleted service.
--
--   **Formalization Note** The residual life $Y_s$ exists only when $P(Y > s) > 0$, so the conclusion is stated for those $s$. Moments are `ℝ≥0∞`-valued series.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 204, Proposition 9.2.3

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.3, p. 204: fix a positive integer `k`. If `E[Y^k] < ∞` then
`E[Y_s^k] < ∞` for every `s ≥ 0` (at which the residual life `Y_s` is defined, `F*(s) > 0`). -/
theorem residual_moment_finite (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (k : ℕ) (hk : 1 ≤ k)
    (hmom : moment u k < ∞) (s : ℕ) (hs : 0 < tail u s) :
    residualMoment u s k < ∞ := by sorry

end SennottDP.ResidualLife
