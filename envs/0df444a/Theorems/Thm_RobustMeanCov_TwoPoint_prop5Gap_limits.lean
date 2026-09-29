-- Prove2me | Theorems.Thm_RobustMeanCov_TwoPoint_prop5Gap_limits
-- name    : RobustMeanCov.TwoPoint.prop5Gap_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:51:20.085397+00:00
-- url     : https://prove2.me/theorems/43f85ac4-be38-4ddd-afd0-d5b64d06e7c6
-- title:
--   Proof of Proposition 5: the limits of $g$ at $-\infty$ and at $\mu^-$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be differentiable with $u'$ inverse S-shaped, and suppose $u'(y)\to\ell_-$ as $y\to-\infty$ and $u'(y)\to\ell_+$ as $y\to+\infty$, with $\ell_\pm\in\mathbb R$. Fix $\mu\in\mathbb R$ and $\sigma>0$, and let $g(y)=\frac{u(z)-u(y)}{z-y}-\frac{u'(y)+u'(z)}{2}$ with $z=\mu+\sigma^2/(\mu-y)$, for $y<\mu$. Then
--   $$
--   \lim_{y\to-\infty}g(y)=\frac{\ell_--u'(\mu)}{2}>0
--   \qquad\text{and}\qquad
--   \lim_{y\to\mu^-}g(y)=\frac{\ell_+-u'(\mu)}{2}<0 .
--   $$
--
--   The sign change of $g$ on $(-\infty,\mu)$ is what produces the two support points in Proposition 5.
--
--   **Formalization Note** The limit at $\mu$ is the left limit (`𝓝[<] μ`), since $g$ is defined on $(-\infty,\mu)$. The limits of $u'$ are explicit arguments with `Tendsto` hypotheses.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 5, left column (the two limits of g)

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_SShaped
import Definitions.Def_RobustMeanCov_TwoPoint_Prop5Gap
open Filter Topology

namespace RobustMeanCov.TwoPoint

/-- Appendix, proof of Proposition 5 (Popescu 2007, p. 110): under the hypotheses of
Proposition 5, with `l₋ = u'(-∞)` and `l₊ = u'(+∞)`, the function `g` tends to
`(l₋ - u'(μ)) / 2 > 0` as `y → -∞` and to `(l₊ - u'(μ)) / 2 < 0` as `y → μ` from the left. -/
theorem prop5Gap_limits (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hinv : IsInverseSShaped (deriv u)) (lm lp : ℝ)
    (hlm : Tendsto (deriv u) atBot (𝓝 lm)) (hlp : Tendsto (deriv u) atTop (𝓝 lp))
    (μ σ : ℝ) (hσ : 0 < σ) :
    Tendsto (prop5Gap u μ σ) atBot (𝓝 ((lm - deriv u μ) / 2)) ∧
      0 < (lm - deriv u μ) / 2 ∧
      Tendsto (prop5Gap u μ σ) (𝓝[<] μ) (𝓝 ((lp - deriv u μ) / 2)) ∧
      (lp - deriv u μ) / 2 < 0 := by sorry

end RobustMeanCov.TwoPoint
