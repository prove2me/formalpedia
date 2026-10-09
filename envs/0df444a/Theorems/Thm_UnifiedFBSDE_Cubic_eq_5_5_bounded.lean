-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_eq_5_5_bounded
-- name    : UnifiedFBSDE.Cubic.eq_5_5_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:42.827279+00:00
-- url     : https://prove2.me/theorems/d36bed71-b773-42a6-9bad-8f063b30f6b6
-- title:
--   (5.5), p. 21 — if σ₂b₃ = 0 and b₂ + f₃σ₂ + b₃σ₁ = 0, (5.3) becomes linear and has a bounded solution
-- statement:
--   Let $F$ be the cubic (5.4), $h\in\mathbb R$ and $T>0$, and suppose
--   $$
--   \sigma_2b_3=0\qquad\text{and}\qquad b_2+f_3\sigma_2+b_3\sigma_1=0 .
--   $$
--   Then $F(y)=f_1+(f_2+b_1+\sigma_1f_3)\,y$ for all $y$, so (5.3) becomes the linear equation
--   $$
--   y_t=h+\int_t^T[f_1+(f_2+b_1+\sigma_1f_3)\,y_s]\,ds, \tag{5.5}
--   $$
--   and (5.5) has a bounded solution on $[0,T]$.
--
--   This is the sufficiency of condition (iii) of Theorem 5.3.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 21, proof of Theorem 5.3, (5.5)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- (5.5), proof of Theorem 5.3, p. 21: in case (iii) the ODE (5.3) becomes the linear
equation (5.5), which has a bounded solution on `[0, T]`. -/
theorem eq_5_5_bounded (c : Coeffs) (h T : ℝ) (hT : 0 < T)
    (h3 : c.σ₂ * c.b₃ = 0) (h2 : c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁ = 0) :
    (∀ y : ℝ, c.F y = c.f₁ + (c.f₂ + c.b₁ + c.σ₁ * c.f₃) * y) ∧
    ∃ y : ℝ → ℝ,
      IsBoundedSolution (fun _ y => c.f₁ + (c.f₂ + c.b₁ + c.σ₁ * c.f₃) * y) h T y := by sorry

end UnifiedFBSDE.Cubic
