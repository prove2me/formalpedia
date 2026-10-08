-- Prove2me | Theorems.Thm_SlowConvergence_Newton_gradient_lower_bound
-- name    : SlowConvergence.Newton.gradient_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:27.780988+00:00
-- url     : https://prove2.me/theorems/2002dd62-b715-4080-967e-43f167dc151a
-- title:
--   §3, p. 6 — the prescribed gradients satisfy (2.3): $\|g_k\| \ge (1/(k+1))^{1/(2-\tau)}$
-- statement:
--   Let $0 < \tau < 1$, $\eta = \tau/(4-2\tau)$, and let $g_k = -\big((1/(k+1))^{\frac12+\eta}, (1/(k+1))^2\big)^T$ be the gradients prescribed by (3.4). Then $\tfrac12 + \eta = \tfrac1{2-\tau}$, and for every $k \ge 0$
--   $$\|g_k\| \;\ge\; \Big(\frac1{k+1}\Big)^{\frac1{2-\tau}} ,$$
--   which is the requirement (2.3).
--
--   This is the inequality that turns the construction into a complexity lower bound: an iterate with $\|g_k\| \le \varepsilon$ can occur only once $k+1 \ge \varepsilon^{-(2-\tau)}$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 6, §3, after (3.4); (2.3) and (2.10), p. 3

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §3, p. 6, after (3.4): "The first part of (3.4) then
immediately gives (2.3) by construction, since the norm of that vector is at least equal to the absolute
value of its first component." With `η = τ/(4 − 2τ)` (2.10), `1/2 + η = 1/(2 − τ)`, and the prescribed
gradient `g_k` of (3.4) satisfies (2.3): `‖g_k‖ ≥ (1/(k+1))^{1/(2−τ)}` for all `k ≥ 0`. -/
theorem gradient_lower_bound (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    1 / 2 + eta τ = 1 / (2 - τ) ∧
      ∀ k : ℕ, (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) ≤ ‖gk τ k‖ := by sorry

end SlowConvergence.Newton
