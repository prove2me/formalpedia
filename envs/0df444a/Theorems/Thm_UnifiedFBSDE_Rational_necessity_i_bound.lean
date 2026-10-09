-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_necessity_i_bound
-- name    : UnifiedFBSDE.Rational.necessity_i_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:43.704168+00:00
-- url     : https://prove2.me/theorems/e16b5c18-4519-426d-8257-e78368ea763b
-- title:
--   Appendix, proof of Theorem 5.6 (Necessity) (i), p. 47 — if α₃ < 0 and F has no zero in (−∞, h], then F(y) ≤ −ε(h + 1 − y)² for all y ≤ h
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients and $\sigma_3\neq0$. Assume $h<\sigma_3^{-1}$, $F(h)\le0$, $\alpha_3=b_2-b_3\sigma_2/\sigma_3<0$, and that $F$ has no zero point in $(-\infty,h]$. Then there is $\varepsilon>0$ with
--   $$
--   F(y)\le-\varepsilon\,(h+1-y)^2\qquad\text{for all }y\le h .
--   $$
--
--   The quadratic upper bound is what drives the solution of the dominating ODE to $-\infty$ in finite time, following the necessity argument of Theorem 5.3.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.6 (Necessity), (i), second paragraph

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Appendix, proof of Theorem 5.6 (Necessity) (i), p. 47: if `h < 1/σ₃`, `F(h) ≤ 0`,
`α₃ < 0` and `F` has no zero point in `(−∞, h]`, then there is `ε > 0` with
`F(y) ≤ −ε (h + 1 − y)²` for all `y ≤ h`. -/
theorem necessity_i_bound (c : Coeffs) (h : ℝ) (hσ : c.σ₃ ≠ 0) (hh : h < 1 / c.σ₃)
    (hFh : c.F h ≤ 0) (hα : c.α₃ < 0) (hnz : ∀ y : ℝ, y ≤ h → c.F y ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, y ≤ h → c.F y ≤ -ε * (h + 1 - y) ^ 2 := by sorry

end UnifiedFBSDE.Rational
