-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_eq_A_6_blowup
-- name    : UnifiedFBSDE.Cubic.eq_A_6_blowup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:15.521822+00:00
-- url     : https://prove2.me/theorems/35e8b279-3b60-4621-85fb-6da0ea2e4ec3
-- title:
--   (A.6) and comparison, p. 47 — if G(y) ≥ ε(y − y₁)³ for y ≥ h and T > 1/(2ε(h − y₁)²), then y_t = h + ∫ₜᵀ G(y_s) ds has no solution on [0, T]
-- statement:
--   Let $\varepsilon>0$, $y_1<h$ and
--   $$
--   T>\frac{1}{2\varepsilon(h-y_1)^2}.
--   $$
--   Let $G:\mathbb R\to\mathbb R$ be continuous with $G(y)\ge\varepsilon(y-y_1)^3$ for all $y\ge h$. Then the backward ODE
--   $$
--   y_t=h+\int_t^T G(y_s)\,ds
--   $$
--   has no solution on $[0,T]$: any solution is bounded below by the solution $\tilde y$ of (A.6), which blows up at $T-1/(2\varepsilon(h-y_1)^2)\in(0,T)$.
--
--   Applied to $G=F$ with the bound (A.4), this is the statement "the solution of (5.3) will blow-up at finite time" in Case 1 of the necessity proof of Theorem 5.3.
--
--   **Formalization Note.** Continuity of $G$ is assumed (the cubic $F$ is a polynomial). It is needed: with $G=-1$ below $h$ and $G(h)=1$ the function $y_t=h-(T-t)$ solves the equation globally.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.3 (Necessity), Case 1, after (A.6)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- (A.6) and the comparison after it, Appendix, p. 47: if `G(y) ≥ ε(y − y₁)³` for `y ≥ h`
and `T > 1/(2ε(h − y₁)²)`, the backward equation with right side `G` and terminal value `h`
has no solution on `[0, T]` (it blows up). Continuity of `G` is a disclosed addition. -/
theorem eq_A_6_blowup (ε y₁ h T : ℝ) (hε : 0 < ε) (hy₁ : y₁ < h)
    (hT : 1 / (2 * ε * (h - y₁) ^ 2) < T) (G : ℝ → ℝ) (hG : Continuous G)
    (hGε : ∀ y : ℝ, h ≤ y → ε * (y - y₁) ^ 3 ≤ G y) :
    ¬ ∃ y : ℝ → ℝ, IsSolution (fun _ y => G y) h T y := by sorry

end UnifiedFBSDE.Cubic
