-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_necessity_iii_bound
-- name    : UnifiedFBSDE.Rational.necessity_iii_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:27.406774+00:00
-- url     : https://prove2.me/theorems/667a6e9a-b9ce-4489-ac50-89ec2156b825
-- title:
--   Appendix, proof of Theorem 5.6 (Necessity) (iii), p. 47 — if α₀ > 0 and F has no zero in [h, σ₃⁻¹), then F(y) ≥ ε(σ₃⁻¹ − y)⁻¹ there
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients, $\sigma_3\neq0$, and let $\alpha_0,\alpha_1,\alpha_2$ give the decomposition (5.8). Assume $h<\sigma_3^{-1}$, $F(h)\ge0$, $\alpha_0>0$, and that $F$ has no zero point in $[h,\sigma_3^{-1})$. Then there is $\varepsilon>0$ with
--   $$
--   F(y)\ge\frac{\varepsilon}{\sigma_3^{-1}-y}\qquad\text{for all }y\in[h,\sigma_3^{-1}).
--   $$
--
--   The lower bound lets the solution of (5.3) be compared with an explicitly solvable equation that reaches the pole in finite time.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.6 (Necessity), (iii), third paragraph

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Appendix, proof of Theorem 5.6 (Necessity) (iii), p. 47: if `h < 1/σ₃`, `F(h) ≥ 0`, the
constant `α₀` of (5.8) is positive and `F` has no zero point in `[h, 1/σ₃)`, then there is
`ε > 0` with `F(y) ≥ ε (1/σ₃ − y)⁻¹` for `y ∈ [h, 1/σ₃)`. -/
theorem necessity_iii_bound (c : Coeffs) (h α₀ α₁ α₂ : ℝ) (hσ : c.σ₃ ≠ 0)
    (hh : h < 1 / c.σ₃) (hFh : 0 ≤ c.F h) (hdec : c.IsDecomp58 α₀ α₁ α₂) (hα₀ : 0 < α₀)
    (hnz : ∀ y : ℝ, h ≤ y → y < 1 / c.σ₃ → c.F y ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, h ≤ y → y < 1 / c.σ₃ → ε * (1 / c.σ₃ - y)⁻¹ ≤ c.F y := by sorry

end UnifiedFBSDE.Rational
