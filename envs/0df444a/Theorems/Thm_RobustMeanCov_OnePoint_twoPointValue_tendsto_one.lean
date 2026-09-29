-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_twoPointValue_tendsto_one
-- name    : RobustMeanCov.OnePoint.twoPointValue_tendsto_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:43:26.094057+00:00
-- url     : https://prove2.me/theorems/bc6acac5-da1c-4fab-905c-e395cc020204
-- title:
--   Appendix (4) — the limit of $U(p,x)$ as $p\to1$ is $u(\mu_x)+\tfrac{\sigma_x^2}{2}\lim_{y\to-\infty}u''(y)$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be concave and twice differentiable with convex derivative $u'$, let $m\in\mathbb R$ and $s>0$, and let $U(p)$ be the two-point objective (8) with mean $m$ and standard deviation $s$.
--
--   1. If $u''(y)\to L\in\mathbb R$ as $y\to-\infty$, then
--   $$
--   \lim_{p\to1^-}U(p)=u(m)+\frac{s^2}{2}\,L .
--   $$
--   2. If $u''(y)\to-\infty$ as $y\to-\infty$, then $U(p)\to-\infty$ as $p\to1^-$.
--
--   Since each $U(p)$ is the expected utility of a law in $\mathbb M_{(m,s^2)}$, this yields the upper bound (4) of the appendix, $U(x)\le u(\mu_x)+\frac{\sigma_x^2}{2}\lim_{y\to-\infty}u''(y)$, and in the second case shows $U(x)=-\infty$.
--
--   **Formalization Note** Under these hypotheses $u''$ is nondecreasing and nonpositive, so its limit at $-\infty$ is either finite or $-\infty$; the two cases are stated separately with explicit limit hypotheses.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 7, (4) and the display preceding it

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue
open Filter Topology

namespace RobustMeanCov.OnePoint

theorem twoPointValue_tendsto_one (u : ℝ → ℝ) (hconc : ConcaveOn ℝ Set.univ u)
    (hu : Differentiable ℝ u) (hu' : Differentiable ℝ (deriv u))
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m s : ℝ) (hs : 0 < s) :
    (∀ L : ℝ, Tendsto (deriv (deriv u)) atBot (𝓝 L) →
      Tendsto (twoPointValue u m s) (𝓝[<] 1) (𝓝 (u m + s ^ 2 / 2 * L))) ∧
    (Tendsto (deriv (deriv u)) atBot atBot →
      Tendsto (twoPointValue u m s) (𝓝[<] 1) atBot) := by sorry

end RobustMeanCov.OnePoint
