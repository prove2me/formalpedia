-- Prove2me | Theorems.Thm_SlowConvergence_Newton_hermite_p_conditions
-- name    : SlowConvergence.Newton.hermite_p_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:42.476551+00:00
-- url     : https://prove2.me/theorems/d326f243-2b7d-4883-abb6-fbe5047ec554
-- title:
--   §3, p. 7 with §2 (2.11)–(2.14), p. 4 — $p_k$ meets the Hermite conditions at $\alpha_k = 1$
-- statement:
--   Let $0 < \tau < 1$, $\eta = \tau/(4-2\tau)$, $\mu_k = (1/(k+1))^{\frac12+\eta}$, and let $p_k$ be the quintic (2.11) with the coefficients of p. 4 and (2.14) in the case $\alpha_k = 1$. Then for every $k \ge 0$
--   $$p_k(0) = \tfrac12\Big(\frac1{k+1}\Big)^{1+2\eta},\qquad p_k(\mu_k) = 0, \tag{2.12}$$
--   $$p_k'(0) = -\Big(\frac1{k+1}\Big)^{\frac12+\eta},\qquad p_k'(\mu_k) = -\Big(\frac1{k+2}\Big)^{\frac12+\eta}, \tag{2.13}$$
--   $$p_k''(0) = p_k''(\mu_k) = 1 .$$
--
--   These are the conditions that make the piecewise function $f_{2,1}$ (equal to $p_k$ on the $k$-th interval, shifted by the next knot value) twice continuously differentiable on $[0,\infty)$, with the values (3.9), slopes $-\mu_k$ and curvature $1$ at the knots required by (3.3)–(3.4).
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 7, §3 (f_{2,1} = f_1 with α_k = 1); p. 4, §2, (2.11)–(2.14)

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, (2.11)–(2.15), p. 4, in the case `α_k = 1` used
for `f_{2,1} = f_1` in §3, p. 7: the quintic `p_k` with coefficients `c_{0,k}, c_{1,k}, c_{2,k}` and
(2.14) satisfies the Hermite conditions on `[0, µ_k]`:
`p_k(0) = ½(1/(k+1))^{1+2η}`, `p_k(µ_k) = 0` (2.12), `p_k'(0) = −(1/(k+1))^{1/2+η}`,
`p_k'(µ_k) = −(1/(k+2))^{1/2+η}` (2.13), and `p_k''(0) = p_k''(µ_k) = 1`. -/
theorem hermite_p_conditions (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    p τ k 0 = 1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ) ∧
      p τ k (mu τ k) = 0 ∧
      deriv (p τ k) 0 = -((1 / ((k : ℝ) + 1)) ^ (1 / 2 + eta τ)) ∧
      deriv (p τ k) (mu τ k) = -((1 / ((k : ℝ) + 2)) ^ (1 / 2 + eta τ)) ∧
      deriv (deriv (p τ k)) 0 = 1 ∧
      deriv (deriv (p τ k)) (mu τ k) = 1 := by sorry

end SlowConvergence.Newton
