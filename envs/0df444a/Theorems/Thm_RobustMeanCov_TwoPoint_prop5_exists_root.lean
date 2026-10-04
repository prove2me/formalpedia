-- Prove2me | Theorems.Thm_RobustMeanCov_TwoPoint_prop5_exists_root
-- name    : RobustMeanCov.TwoPoint.prop5_exists_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:51:55.829217+00:00
-- url     : https://prove2.me/theorems/2be12cfd-6c8b-46fb-bdc4-8b9dec89e640
-- title:
--   Proof of Proposition 5: a zero $a$ of $g$ gives conditions (a) and (b) of Lemma 1
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be differentiable with $u'$ inverse S-shaped and with finite limits at $\pm\infty$. For every $\mu\in\mathbb R$ and $\sigma>0$ there exists $a<\mu$ with $g(a)=0$, where $g$ is the function of the proof of Proposition 5. Setting $b=\mu+\sigma^2/(\mu-a)$, one has $a<b$ and
--   $$
--   (b-\mu)(\mu-a)=\sigma^2,\qquad \frac{u(b)-u(a)}{b-a}=\frac{u'(a)+u'(b)}{2},
--   $$
--   i.e. conditions (a) and (b) of Lemma 1 hold with $q_a=u'(a)$ and $q_b=u'(b)$.
--
--   It remains, for Proposition 5, to show that the resulting quadratic supports $u$ for a suitable such pair.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 5, left column, last paragraph

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_SShaped
import Definitions.Def_RobustMeanCov_TwoPoint_Prop5Gap
open Filter Topology

namespace RobustMeanCov.TwoPoint

/-- Appendix, proof of Proposition 5 (Popescu 2007, p. 110): under the hypotheses of
Proposition 5, for every `μ` and `σ > 0` there is `a < μ` with `g(a) = 0`; with
`b = μ + σ² / (μ - a)` one has `a < b`, condition (a) `(b - μ)(μ - a) = σ²` and condition (b)
`(u(b) - u(a)) / (b - a) = (u'(a) + u'(b)) / 2` of Lemma 1 with `q_a = u'(a)`, `q_b = u'(b)`. -/
theorem prop5_exists_root (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hinv : IsInverseSShaped (deriv u))
    (hbot : ∃ l : ℝ, Tendsto (deriv u) atBot (𝓝 l))
    (htop : ∃ l : ℝ, Tendsto (deriv u) atTop (𝓝 l))
    (μ σ : ℝ) (hσ : 0 < σ) :
    ∃ a b : ℝ, a < μ ∧ b = partnerPoint μ σ a ∧ prop5Gap u μ σ a = 0 ∧ a < b ∧
      (b - μ) * (μ - a) = σ ^ 2 ∧
      (u b - u a) / (b - a) = (deriv u a + deriv u b) / 2 := by sorry

end RobustMeanCov.TwoPoint
