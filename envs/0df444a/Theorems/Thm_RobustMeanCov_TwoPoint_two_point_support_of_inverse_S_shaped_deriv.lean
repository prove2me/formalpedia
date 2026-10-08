-- Prove2me | Theorems.Thm_RobustMeanCov_TwoPoint_two_point_support_of_inverse_S_shaped_deriv
-- name    : RobustMeanCov.TwoPoint.two_point_support_of_inverse_S_shaped_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:52:30.423514+00:00
-- url     : https://prove2.me/theorems/9226d877-aa88-4880-a3e5-6ef85b64b7f9
-- title:
--   Proposition 5: an inverse S-shaped derivative with finite limits gives two-point support
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be differentiable, and suppose its derivative $u'$ is inverse S-shaped — decreasing, concave on $(-\infty,x_0)$ and convex on $(x_0,\infty)$ for some $x_0$ — with finite limits
--   $$
--   \lim_{y\to-\infty}u'(y)\in\mathbb R,\qquad \lim_{y\to+\infty}u'(y)\in\mathbb R .
--   $$
--   Then $u$ satisfies the two-point support property: for every $\mu\in\mathbb R$ and $\sigma>0$ there are $a<b$ and a quadratic $q\le u$ with $q(a)=u(a)$, $q(b)=u(b)$, and a law with mean $\mu$, variance $\sigma^2$ and support $\{a,b\}$.
--
--   Consequently, for such $u$, the worst-case expected utility over all laws with mean $\mu$ and variance $\sigma^2$ reduces to a one-dimensional minimization over two-point laws (Proposition 4 of the paper). Examples include the log-logistic function $u(x)=C+\log\frac{1}{1+e^{-ax}}$ and the catenary $u(x)=C-b\cosh(ax)$ plus a concave quadratic.
--
--   **Formalization Note** "Decreasing" is strict (`StrictAnti` after unfolding `IsInverseSShaped`), the paper's reading of "increasing" in Definition 2. No continuity of $u'$ is assumed beyond what the hypotheses imply.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 102, Proposition 5; proof in the Appendix, p. 110

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_SShaped
import Definitions.Def_RobustMeanCov_TwoPoint_TwoPointSupport
open Filter Topology

namespace RobustMeanCov.TwoPoint

/-- Proposition 5 (Popescu 2007, p. 102): if `u` is differentiable and `u'` is inverse S-shaped
with finite limits at `±∞`, then `u` satisfies the two-point support property. -/
theorem two_point_support_of_inverse_S_shaped_deriv (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hinv : IsInverseSShaped (deriv u))
    (hbot : ∃ l : ℝ, Tendsto (deriv u) atBot (𝓝 l))
    (htop : ∃ l : ℝ, Tendsto (deriv u) atTop (𝓝 l)) :
    TwoPointSupport u := by sorry

end RobustMeanCov.TwoPoint
