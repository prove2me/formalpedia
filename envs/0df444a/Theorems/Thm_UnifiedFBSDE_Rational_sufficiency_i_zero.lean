-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_sufficiency_i_zero
-- name    : UnifiedFBSDE.Rational.sufficiency_i_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:39.212496+00:00
-- url     : https://prove2.me/theorems/3a899aa5-7968-4884-8093-112cbc43f3c5
-- title:
--   Proof of Theorem 5.6 (i), p. 23 — if h < 1/σ₃, F(h) ≤ 0 and F(λ) = 0 with λ ≤ h, then (5.3) has a solution y ∈ [λ, h] for every T
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients, $\sigma_3\neq0$, and let $h<1/\sigma_3$ with $F(h)\le0$. Suppose $F(\lambda)=0$ for some $\lambda\le h$. Then for every $T>0$ the backward ODE
--   $$
--   y_t=h+\int_t^TF(y_s)\,ds,\qquad t\in[0,T],
--   $$
--   has a solution with $\lambda\le y_t\le h$ for all $t\in[0,T]$; in particular $y$ and $(1-\sigma_3y)^{-1}$ are bounded, i.e. (5.9) holds.
--
--   This is the first half of the sufficiency of case (i) in Theorem 5.6.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 23, proof of Theorem 5.6, (i), first sentence

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Proof of Theorem 5.6, sufficiency (i), first case, p. 23: if `h < 1/σ₃`, `F(h) ≤ 0` and
`F(λ) = 0` for some `λ ≤ h`, then for every `T > 0` the ODE (5.3) has a solution with values
in `[λ, h]`, hence satisfying (5.9). -/
theorem sufficiency_i_zero (c : Coeffs) (h l : ℝ) (hσ : c.σ₃ ≠ 0) (hh : h < 1 / c.σ₃)
    (hFh : c.F h ≤ 0) (hl : l ≤ h) (hFl : c.F l = 0) :
    ∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ, IsSolution59 c h T y ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, l ≤ y t ∧ y t ≤ h := by sorry

end UnifiedFBSDE.Rational
