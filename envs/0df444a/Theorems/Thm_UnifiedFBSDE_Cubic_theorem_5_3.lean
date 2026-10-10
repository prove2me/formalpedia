-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_theorem_5_3
-- name    : UnifiedFBSDE.Cubic.theorem_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:47.134837+00:00
-- url     : https://prove2.me/theorems/9dd7ec8d-6bee-43c3-b44c-54860adfab60
-- title:
--   Theorem 5.3, p. 21 — the dominating ODE with cubic F has a bounded solution for every T iff (i), (ii) or (iii)
-- statement:
--   Consider the linear FBSDE (4.1) with constant coefficients and $\sigma_3=0$, terminal coefficient $h\in\mathbb R$, and its dominating ODE
--   $$
--   y_t=h+\int_t^T F(y_s)\,ds,\qquad F(y)=f_1+[f_2+b_1+\sigma_1f_3]y+[b_2+f_3\sigma_2+b_3\sigma_1]y^2+\sigma_2b_3y^3. \tag{5.3–5.4}
--   $$
--   Then (5.3) has a bounded solution on $[0,T]$ for every $T>0$ if and only if one of the following holds:
--   1. $F(h)\ge0$ and $F$ has a zero in $[h,\infty)$;
--   2. $F(h)\le0$ and $F$ has a zero in $(-\infty,h]$;
--   3. $\sigma_2b_3=0$ and $b_2+f_3\sigma_2+b_3\sigma_1=0$.
--
--   This is a sharp, checkable criterion for the existence of a bounded solution of the dominating ODE on an arbitrarily long horizon. In the paper's framework that solution yields a regular decoupling field, and with it well-posedness of the linear FBSDE. In this sense the result marks the limits of solvability for general FBSDEs.
--
--   **Formalization Note.** "For arbitrary $T$" is a universal quantifier over $T>0$ placed outside the existential over $y$. A solution requires the integrand to be integrable on every $[t,T]$ (see the definition file). The page's "zero point in $[h,\infty)$" is $\exists\,l\ge h$ with $F(l)=0$, and similarly for $(-\infty,h]$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 21, Theorem 5.3

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- Theorem 5.3, p. 21. -/
theorem theorem_5_3 (c : Coeffs) (h : ℝ) :
    (∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ, IsBoundedSolution (fun _ y => c.F y) h T y) ↔
      ((0 ≤ c.F h ∧ ∃ l : ℝ, h ≤ l ∧ c.F l = 0) ∨
        (c.F h ≤ 0 ∧ ∃ l : ℝ, l ≤ h ∧ c.F l = 0) ∨
        (c.σ₂ * c.b₃ = 0 ∧ c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁ = 0)) := by sorry

end UnifiedFBSDE.Cubic
