-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_eq_A_4
-- name    : UnifiedFBSDE.Cubic.eq_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:08.78799+00:00
-- url     : https://prove2.me/theorems/223c7105-2950-4e6f-a271-d2cde75a5f76
-- title:
--   (A.4), p. 46 — if a₃ = σ₂b₃ > 0 and F has no zero in [h, ∞), then F(y) ≥ ε(y − y₁)³ for all y ≥ h, for some ε > 0, y₁ < h
-- statement:
--   Let $F(y)=f_1+a_1y+a_2y^2+a_3y^3$ be the cubic (5.4), written as in (A.3), and let $h\in\mathbb R$. Assume $a_3=\sigma_2b_3>0$ and that $F$ has no zero in $[h,\infty)$. Then there exist $\varepsilon>0$ and $y_1<h$ such that
--   $$
--   F(y)\ \ge\ \varepsilon\,(y-y_1)^3\qquad\text{for all }y\ge h. \tag{A.4}
--   $$
--
--   This cubic lower bound is what forces the solution of (5.3) to blow up in finite time in Case 1 of the necessity proof of Theorem 5.3.
--
--   **Formalization Note.** The intermediate inequality (A.5) of the paper is not stated; as printed it does not hold for every ordering of the roots. (A.4) itself is the claim of this milestone.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 46, Appendix, proof of Theorem 5.3 (Necessity), Case 1, (A.3)–(A.4)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- (A.4), Appendix, proof of Theorem 5.3 (Necessity), Case 1, p. 46. -/
theorem eq_A_4 (c : Coeffs) (h : ℝ) (ha₃ : 0 < c.a₃)
    (hno : ∀ l : ℝ, h ≤ l → c.F l ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ y₁ : ℝ, y₁ < h ∧ ∀ y : ℝ, h ≤ y → ε * (y - y₁) ^ 3 ≤ c.F y := by sorry

end UnifiedFBSDE.Cubic
