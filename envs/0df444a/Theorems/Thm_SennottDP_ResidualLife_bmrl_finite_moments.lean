-- Prove2me | Theorems.Thm_SennottDP_ResidualLife_bmrl_finite_moments
-- name    : SennottDP.ResidualLife.bmrl_finite_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T10:32:32.575298+00:00
-- url     : https://prove2.me/theorems/cbb2199d-ab51-42a7-a8c4-5055203cd624
-- title:
--   Proposition 9.2.5 — bounded mean residual lifetimes imply finite moments of all orders
-- statement:
--   Let $Y$ take values in $\{1,2,\dots\}$ with distribution $u_y = P(Y=y)$ and tail $F^*(y) = P(Y>y)$. For $s \ge 0$ with $F^*(s) > 0$ let $Y_s$ be the residual life, $P(Y_s = y) = u_{s+y}/F^*(s)$, $y \ge 1$. Suppose the distribution of $Y$ is BMRL: there is a finite constant $U$ with $E[Y_s] \le U$ for every such $s$. Then
--   $$E[Y^k] < \infty \qquad \text{for every } k \ge 0.$$
--
--   A uniform bound on the expected remaining service time is a first-moment condition on the family of residual lives; the proposition shows that it controls every moment of the service time itself. It is used to verify the assumptions for the average cost optimization of queueing models whose service times are drawn from such distributions.
--
--   **Formalization Note** Moments are `ℝ≥0∞`-valued series ("finite" means `< ⊤`). BMRL is required only at those $s$ with $P(Y > s) > 0$, where the residual life is defined; $U$ is a finite nonnegative real.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 204, Proposition 9.2.5 (with Definition 9.2.4)

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.5, p. 204: if the distribution of `Y` (on `{1, 2, …}`) has
bounded mean residual lifetimes, then `Y` has finite moments of all orders. -/
theorem bmrl_finite_moments (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (hbmrl : IsBMRLDist u) :
    ∀ k : ℕ, moment u k < ∞ := by sorry

end SennottDP.ResidualLife
