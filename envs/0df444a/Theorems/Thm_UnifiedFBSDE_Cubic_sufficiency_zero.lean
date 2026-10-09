-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_sufficiency_zero
-- name    : UnifiedFBSDE.Cubic.sufficiency_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:09.435995+00:00
-- url     : https://prove2.me/theorems/365c8497-8c87-4509-a178-21cb9611903a
-- title:
--   Proof of Theorem 5.3, p. 21 — if F(h) ≥ 0 and F(λ) = 0 for some λ ≥ h, (5.3) has a solution with y_t ∈ [h, λ]; symmetrically for F(h) ≤ 0
-- statement:
--   Let $F$ be the cubic (5.4), $h\in\mathbb R$ and $T>0$.
--
--   1. If $F(h)\ge0$ and $F(\lambda)=0$ for some $\lambda\ge h$, then the dominating ODE
--   $$
--   y_t=h+\int_t^T F(y_s)\,ds \tag{5.3}
--   $$
--   has a solution on $[0,T]$ with $h\le y_t\le\lambda$ for all $t\in[0,T]$.
--   2. If $F(h)\le0$ and $F(\lambda)=0$ for some $\lambda\le h$, then (5.3) has a solution on $[0,T]$ with $\lambda\le y_t\le h$ for all $t\in[0,T]$.
--
--   In both cases the solution is bounded by constants independent of $T$, which gives the sufficiency of conditions (i) and (ii) of Theorem 5.3.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 21, proof of Theorem 5.3, first paragraph

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- Proof of Theorem 5.3, p. 21, first paragraph (sufficiency in cases (i) and (ii)). -/
theorem sufficiency_zero (c : Coeffs) (h T : ℝ) (hT : 0 < T) :
    (∀ l : ℝ, 0 ≤ c.F h → h ≤ l → c.F l = 0 →
      ∃ y : ℝ → ℝ, IsSolution (fun _ y => c.F y) h T y ∧
        ∀ t ∈ Set.Icc 0 T, h ≤ y t ∧ y t ≤ l) ∧
    (∀ l : ℝ, c.F h ≤ 0 → l ≤ h → c.F l = 0 →
      ∃ y : ℝ → ℝ, IsSolution (fun _ y => c.F y) h T y ∧
        ∀ t ∈ Set.Icc 0 T, l ≤ y t ∧ y t ≤ h) := by sorry

end UnifiedFBSDE.Cubic
