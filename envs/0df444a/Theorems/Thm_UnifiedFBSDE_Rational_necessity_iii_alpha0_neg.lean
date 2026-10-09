-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_necessity_iii_alpha0_neg
-- name    : UnifiedFBSDE.Rational.necessity_iii_alpha0_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:13.907435+00:00
-- url     : https://prove2.me/theorems/5446865f-5d28-47ee-9867-80883b883fc2
-- title:
--   Appendix, proof of Theorem 5.6 (Necessity) (iii), p. 47 — if h < σ₃⁻¹, F(h) ≥ 0 and α₀ < 0 in (5.8), then F has a zero point in [h, σ₃⁻¹)
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients, $\sigma_3\neq0$, and let $\alpha_0,\alpha_1,\alpha_2$ be constants giving the decomposition (5.8),
--   $$
--   F(y)=\frac{\alpha_0}{1/\sigma_3-y}+\alpha_1+\alpha_2y+\Big[b_2-\frac{b_3\sigma_2}{\sigma_3}\Big]y^2\qquad(1-\sigma_3y\neq0).
--   $$
--   If $h<\sigma_3^{-1}$, $F(h)\ge0$ and $\alpha_0<0$, then there is $\lambda\in[h,\sigma_3^{-1})$ with $F(\lambda)=0$.
--
--   With $\alpha_0<0$, $F(y)\to-\infty$ as $y\uparrow\sigma_3^{-1}$; this is the easy branch of the necessity of case (iii).
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.6 (Necessity), (iii), second paragraph

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Appendix, proof of Theorem 5.6 (Necessity) (iii), p. 47: if `h < 1/σ₃`, `F(h) ≥ 0` and the
constant `α₀` of (5.8) is negative, then `F` has a zero point in `[h, 1/σ₃)`. -/
theorem necessity_iii_alpha0_neg (c : Coeffs) (h α₀ α₁ α₂ : ℝ) (hσ : c.σ₃ ≠ 0)
    (hh : h < 1 / c.σ₃) (hFh : 0 ≤ c.F h) (hdec : c.IsDecomp58 α₀ α₁ α₂) (hα₀ : α₀ < 0) :
    ∃ l : ℝ, h ≤ l ∧ l < 1 / c.σ₃ ∧ c.F l = 0 := by sorry

end UnifiedFBSDE.Rational
