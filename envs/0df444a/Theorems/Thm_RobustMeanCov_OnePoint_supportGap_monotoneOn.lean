-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_supportGap_monotoneOn
-- name    : RobustMeanCov.OnePoint.supportGap_monotoneOn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:45:57.44602+00:00
-- url     : https://prove2.me/theorems/6d5ca443-3e5b-4a86-a4f9-7640c67f2811
-- title:
--   Proof of Proposition 7 — the slope function $d(y)$ is nondecreasing
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be differentiable with convex derivative $u'$, and let $m\in\mathbb R$. For $y\ne m$ put
--
--   $$
--   d(y)=\frac{u(y)-u(m)}{(y-m)^2}-\frac{u'(m)}{y-m}.
--   $$
--
--   Then $d$ is nondecreasing on its domain $\{y\in\mathbb{R} : y\neq m\}$: $d(y)\le d(y')$ whenever $y\le y'$ and $y,y'\neq m$, including $y<m<y'$.
--
--   In the proof of Proposition 7, $d(y)\ge c$ for all $y\neq m$ is exactly the statement that the quadratic $c(y-m)^2+u'(m)(y-m)+u(m)$ lies below $u$, so the monotonicity of $d$ reduces the support question to the behaviour of $d$ at $-\infty$.
--
--   **Formalization Note** $d$ is undefined at $y=m$, so monotonicity is stated on $\{y\neq m\}$ (Lean's `MonotoneOn` on that set, which compares points on both sides of $m$, as the proof's $\inf_y d(y)=\lim_{y\to-\infty}d(y)$ requires). The page's second denominator "$y-\mu$" is read as $y-\mu_x$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 7, definition of d(y) and the display of d′(y)

import Mathlib

namespace RobustMeanCov.OnePoint

theorem supportGap_monotoneOn (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m : ℝ) :
    MonotoneOn (fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) {y : ℝ | y ≠ m} := by sorry

end RobustMeanCov.OnePoint
