-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_remark_5_2
-- name    : UnifiedFBSDE.Cubic.remark_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:16.221238+00:00
-- url     : https://prove2.me/theorems/c975ac03-8595-497e-b79d-65b818e7aea4
-- title:
--   Remark 5.2, p. 20 — Cⁱ ≥ ∫₀ᵀ e^{L(T−t)}(cⁱₜ)⁺ dt, in particular Cⁱ = 0 and cⁱ ≤ 0, implies condition (iv) of Lemma 5.1
-- statement:
--   Let $T>0$, $L\ge0$ and $c:\mathbb R\to\mathbb R$.
--
--   1. If $c$ is integrable on $[0,T]$ and
--   $$
--   C\ \ge\ \int_0^T e^{L(T-t)}\,(c_t)^+\,dt,
--   $$
--   then for every measurable $\alpha$ with $|\alpha|\le L$ and every $t\in[0,T]$,
--   $C\ge\int_t^T e^{-\int_s^T\alpha_r\,dr}c_s\,ds$, i.e. $(C,c)$ satisfies condition (iv) of Lemma 5.1.
--   2. If $c_t\le0$ for all $t\in[0,T]$, then $(0,c)$ satisfies condition (iv).
--
--   This makes condition (iv) checkable in practice; the second case is the one used when the comparison functions of Lemma 5.1 are exact solutions or constants.
--
--   **Formalization Note.** Integrability of $c$ on $[0,T]$ is assumed in part 1 so that both sides are genuine integrals.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 20, Remark 5.2

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- Remark 5.2, p. 20: `C ≥ ∫₀ᵀ e^{L(T−t)} (c_t)⁺ dt` is sufficient for condition (iv) of
Lemma 5.1, and so is `C = 0, c ≤ 0`. -/
theorem remark_5_2 (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L) (c : ℝ → ℝ) :
    (∀ C : ℝ, MeasureTheory.IntegrableOn c (Set.Icc 0 T) →
      ∫ t in (0 : ℝ)..T, Real.exp (L * (T - t)) * max (c t) 0 ≤ C → CondIV L C c T) ∧
    ((∀ t ∈ Set.Icc 0 T, c t ≤ 0) → CondIV L 0 c T) := by sorry

end UnifiedFBSDE.Cubic
