-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_case_2_blowup
-- name    : UnifiedFBSDE.Cubic.case_2_blowup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:26.568181+00:00
-- url     : https://prove2.me/theorems/afa58020-cd3f-4dd3-8fcb-31d33b91c318
-- title:
--   Case 2, p. 47 — if a₃ = 0, a₂ > 0, F(h) > 0 and F has no zero in [h, ∞), then F(y) ≥ ε(y − y₁)² for y ≥ h and (5.3) blows up for large T
-- statement:
--   Let $F(y)=f_1+a_1y+a_2y^2+a_3y^3$ be the cubic (5.4), written as in (A.3), and let $h\in\mathbb R$. Assume $a_3=0$, $a_2>0$, $F(h)>0$, and that $F$ has no zero in $[h,\infty)$. Then:
--   1. there exist $\varepsilon>0$ and $y_1<h$ with
--   $$
--   F(y)\ \ge\ \varepsilon\,(y-y_1)^2\qquad\text{for all }y\ge h;
--   $$
--   2. there is $T_0$ such that for every $T>T_0$ the dominating ODE (5.3), $y_t=h+\int_t^TF(y_s)\,ds$, has no solution on $[0,T]$.
--
--   This is the second case of the necessity proof of Theorem 5.3: a quadratic $F$ with positive leading coefficient and no zero above $h$ makes the solution explode once the horizon is long enough.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.3 (Necessity), Case 2

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- Case 2, Appendix, proof of Theorem 5.3 (Necessity), p. 47. -/
theorem case_2_blowup (c : Coeffs) (h : ℝ) (ha₃ : c.a₃ = 0) (ha₂ : 0 < c.a₂)
    (hno : ∀ l : ℝ, h ≤ l → c.F l ≠ 0) (hFh : 0 < c.F h) :
    (∃ ε : ℝ, 0 < ε ∧ ∃ y₁ : ℝ, y₁ < h ∧ ∀ y : ℝ, h ≤ y → ε * (y - y₁) ^ 2 ≤ c.F y) ∧
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ < T → ¬ ∃ y : ℝ → ℝ, IsSolution (fun _ y => c.F y) h T y := by sorry

end UnifiedFBSDE.Cubic
