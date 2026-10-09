-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_sufficiency_i_alpha3
-- name    : UnifiedFBSDE.Rational.sufficiency_i_alpha3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:02.491664+00:00
-- url     : https://prove2.me/theorems/b6b6a3df-1131-4395-ac2c-bf971321c0c1
-- title:
--   Proof of Theorem 5.6 (i), p. 23 — if h < 1/σ₃, F(h) ≤ 0 and b₂ − b₃σ₂/σ₃ = 0, then (5.3) has a solution y ≤ h satisfying (5.9) for every T
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients, $\sigma_3\neq0$, $h<1/\sigma_3$ and $F(h)\le0$, and suppose
--   $$
--   b_2-\frac{b_3\sigma_2}{\sigma_3}=0 .
--   $$
--   Then for every $T>0$ the backward ODE $y_t=h+\int_t^TF(y_s)\,ds$ has a solution on $[0,T]$ with $y_t\le h$ for all $t$, such that $y$ and $(1-\sigma_3y)^{-1}$ are bounded on $[0,T]$ (condition (5.9)).
--
--   With $\alpha_3=0$ the function $F$ grows at most linearly as $y\to-\infty$, so no zero of $F$ is needed; this is the second half of the sufficiency of case (i) in Theorem 5.6.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 23, proof of Theorem 5.6, (i), from "We now assume instead"

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Proof of Theorem 5.6, sufficiency (i), second case, p. 23: if `h < 1/σ₃`, `F(h) ≤ 0` and
`b₂ − b₃σ₂/σ₃ = 0`, then for every `T > 0` the ODE (5.3) has a solution with `y ≤ h`
satisfying (5.9). -/
theorem sufficiency_i_alpha3 (c : Coeffs) (h : ℝ) (hσ : c.σ₃ ≠ 0) (hh : h < 1 / c.σ₃)
    (hFh : c.F h ≤ 0) (hα : c.α₃ = 0) :
    ∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ, IsSolution59 c h T y ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, y t ≤ h := by sorry

end UnifiedFBSDE.Rational
