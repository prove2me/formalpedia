-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_quadratic_five_supports
-- name    : RobustMeanCov.OnePoint.quadratic_five_supports
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:46:43.194978+00:00
-- url     : https://prove2.me/theorems/948fba5c-293b-4728-a2c9-2d5152649b2e
-- title:
--   Appendix (5) — the quadratic $\tfrac12u''(-\infty)(y-\mu_x)^2+u'(\mu_x)(y-\mu_x)+u(\mu_x)$ supports $u$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be concave and twice differentiable with convex derivative $u'$, and suppose $u''(y)\to L\in\mathbb R$ as $y\to-\infty$. Fix $m\in\mathbb R$ and let $d(y)=\frac{u(y)-u(m)}{(y-m)^2}-\frac{u'(m)}{y-m}$ for $y\neq m$. Then
--
--   1. the quadratic (5)
--   $$
--   q(y)=\tfrac12 L\,(y-m)^2+u'(m)(y-m)+u(m)
--   $$
--   supports $u$: $q(y)\le u(y)$ for every $y\in\mathbb R$;
--   2. $\inf_{y\neq m}d(y)=\tfrac12 L$, i.e. $\tfrac12L$ is the greatest lower bound of $\{d(y):y\ne m\}$;
--   3. $d(y)\to\tfrac12L$ as $y\to-\infty$.
--
--   For every law of mean $m$ and variance $s^2$ one has $E[q(r)]=u(m)+\frac{s^2}{2}L$, so with Proposition 3 this gives the lower bound matching (4) in the proof of Proposition 7(a).
--
--   **Formalization Note** $L$ is the paper's $u''(-\infty)$, taken as an explicit finite limit hypothesis.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 7, (5) and the paragraph following it

import Mathlib
open Filter Topology

namespace RobustMeanCov.OnePoint

theorem quadratic_five_supports (u : ℝ → ℝ) (hconc : ConcaveOn ℝ Set.univ u)
    (hu : Differentiable ℝ u) (hu' : Differentiable ℝ (deriv u))
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (L : ℝ)
    (hL : Tendsto (deriv (deriv u)) atBot (𝓝 L)) (m : ℝ) :
    (∀ y : ℝ, 1 / 2 * L * (y - m) ^ 2 + deriv u m * (y - m) + u m ≤ u y) ∧
    IsGLB ((fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) '' {y | y ≠ m})
      (1 / 2 * L) ∧
    Tendsto (fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) atBot
      (𝓝 (1 / 2 * L)) := by sorry

end RobustMeanCov.OnePoint
