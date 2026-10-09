-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_necessity_i_alpha_pos
-- name    : UnifiedFBSDE.Rational.necessity_i_alpha_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:27.882826+00:00
-- url     : https://prove2.me/theorems/00159d56-f67a-4ecb-a19b-37c1a3a3672a
-- title:
--   Appendix, proof of Theorem 5.6 (Necessity) (i), p. 47 — if h < σ₃⁻¹, F(h) ≤ 0 and α₃ > 0, then F has a zero point in (−∞, h]
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients and $\sigma_3\neq0$. If $h<\sigma_3^{-1}$, $F(h)\le0$ and
--   $$
--   \alpha_3=b_2-\frac{b_3\sigma_2}{\sigma_3}>0,
--   $$
--   then there is $\lambda\le h$ with $F(\lambda)=0$.
--
--   This is the easy branch of the necessity of case (i) in Theorem 5.6: when $\alpha_3>0$, $F(y)\to+\infty$ as $y\to-\infty$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.6 (Necessity), (i), second paragraph

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Appendix, proof of Theorem 5.6 (Necessity) (i), p. 47: if `h < 1/σ₃`, `F(h) ≤ 0` and
`α₃ > 0`, then `F` has a zero point in `(−∞, h]`. -/
theorem necessity_i_alpha_pos (c : Coeffs) (h : ℝ) (hσ : c.σ₃ ≠ 0) (hh : h < 1 / c.σ₃)
    (hFh : c.F h ≤ 0) (hα : 0 < c.α₃) :
    ∃ l : ℝ, l ≤ h ∧ c.F l = 0 := by sorry

end UnifiedFBSDE.Rational
