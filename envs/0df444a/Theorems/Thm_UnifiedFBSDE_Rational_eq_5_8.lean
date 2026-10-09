-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_eq_5_8
-- name    : UnifiedFBSDE.Rational.eq_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:05.796657+00:00
-- url     : https://prove2.me/theorems/d0901b85-479a-4165-ab2f-c5cb0ee79df9
-- title:
--   (5.8), p. 22 — for σ₃ ≠ 0, F(y) = α₀/(1/σ₃ − y) + α₁ + α₂y + [b₂ − b₃σ₂/σ₃]y² for some constants α₀, α₁, α₂
-- statement:
--   Let $F$ be the function (3.9) of the linear FBSDE with constant coefficients $b_i,\sigma_i,f_i$ ($i=1,2,3$), and assume $\sigma_3\neq0$. Then there are real constants $\alpha_0,\alpha_1,\alpha_2$ such that for every $y$ with $1-\sigma_3y\neq0$,
--   $$
--   F(y)=\frac{\alpha_0}{1/\sigma_3-y}+\alpha_1+\alpha_2y+\Big[b_2-\frac{b_3\sigma_2}{\sigma_3}\Big]y^2 .
--   $$
--
--   This partial-fraction form separates the pole term, governed by $\alpha_0$, from the quadratic growth at infinity, governed by $\alpha_3=b_2-b_3\sigma_2/\sigma_3$; the four cases of Theorem 5.6 are read off from these two coefficients.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 22, (5.8)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- (5.8), p. 22: for `σ₃ ≠ 0` there are constants `α₀, α₁, α₂` with
`F(y) = α₀/(1/σ₃ − y) + α₁ + α₂ y + [b₂ − b₃σ₂/σ₃] y²` off the pole. -/
theorem eq_5_8 (c : Coeffs) (hσ : c.σ₃ ≠ 0) :
    ∃ α₀ α₁ α₂ : ℝ, c.IsDecomp58 α₀ α₁ α₂ := by sorry

end UnifiedFBSDE.Rational
