-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_sufficiency_iii
-- name    : UnifiedFBSDE.Rational.sufficiency_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:12.486832+00:00
-- url     : https://prove2.me/theorems/35e68c17-d98c-4692-bf37-5a98df99edf5
-- title:
--   Proof of Theorem 5.6 (iii), p. 23 — if h < 1/σ₃, F(h) ≥ 0 and F(λ) = 0 with λ ∈ [h, 1/σ₃), then h ≤ y_t ≤ λ solves (5.3) for every T
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients, $\sigma_3\neq0$, $h<1/\sigma_3$ and $F(h)\ge0$. Suppose $F(\lambda)=0$ for some $\lambda\in[h,1/\sigma_3)$. Then for every $T>0$ the backward ODE $y_t=h+\int_t^TF(y_s)\,ds$ has a solution on $[0,T]$ with
--   $$
--   h\le y_t\le\lambda\qquad\text{for all }t\in[0,T],
--   $$
--   and hence (5.9) holds: $y$ and $(1-\sigma_3y)^{-1}$ are bounded.
--
--   This is the sufficiency of case (iii) in Theorem 5.6: the zero $\lambda$ shields the solution from the pole $1/\sigma_3$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 23, proof of Theorem 5.6, (iii)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Proof of Theorem 5.6, sufficiency (iii), p. 23: if `h < 1/σ₃`, `F(h) ≥ 0` and `F(λ) = 0`
for some `λ ∈ [h, 1/σ₃)`, then for every `T > 0` the ODE (5.3) has a solution with
`h ≤ y_t ≤ λ`, hence satisfying (5.9). -/
theorem sufficiency_iii (c : Coeffs) (h l : ℝ) (hσ : c.σ₃ ≠ 0) (hh : h < 1 / c.σ₃)
    (hFh : 0 ≤ c.F h) (hl : h ≤ l) (hl' : l < 1 / c.σ₃) (hFl : c.F l = 0) :
    ∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ, IsSolution59 c h T y ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, h ≤ y t ∧ y t ≤ l := by sorry

end UnifiedFBSDE.Rational
