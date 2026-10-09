-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_eq_A_6_solution
-- name    : UnifiedFBSDE.Cubic.eq_A_6_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:23.828045+00:00
-- url     : https://prove2.me/theorems/02c5d2b9-c8f8-4da6-860d-0b2445605427
-- title:
--   (A.6), p. 47 — the explicit solution ỹₜ − y₁ = (2ε(t − T) + (h − y₁)⁻²)^{−1/2}, which blows up at t = T − 1/(2ε(h − y₁)²) ∈ (0, T)
-- statement:
--   Let $\varepsilon>0$ and $y_1<h$, let $T\in\mathbb R$, and put
--   $$
--   t_0=T-\frac{1}{2\varepsilon(h-y_1)^2},\qquad \tilde y_t=y_1+\frac{1}{\sqrt{2\varepsilon(t-T)+(h-y_1)^{-2}}}\quad(t>t_0).
--   $$
--   Then:
--   1. for every $t\in(t_0,T]$ the function $\tilde y$ solves
--   $$
--   \tilde y_t=h+\int_t^T\varepsilon(\tilde y_s-y_1)^3\,ds, \tag{A.6}
--   $$
--   with an integrable integrand on $[t,T]$;
--   2. $\tilde y_t\to+\infty$ as $t\downarrow t_0$;
--   3. if $T>\dfrac{1}{2\varepsilon(h-y_1)^2}$, then $t_0\in(0,T)$.
--
--   So the comparison equation (A.6) explodes inside $[0,T]$ as soon as $T$ exceeds $1/(2\varepsilon(h-y_1)^2)$.
--
--   **Formalization Note.** The paper writes the integrand of (A.6) with the dummy variable $t$; it is read as $\int_t^T\varepsilon(\tilde y_s-y_1)^3\,ds$. The formula for $\tilde y$ is only used for $t>t_0$, where the square root is of a positive number.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 47, Appendix, proof of Theorem 5.3 (Necessity), Case 1, (A.6)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- (A.6), Appendix, p. 47: the explicit solution
`ỹ_t − y₁ = 1/√(2ε(t − T) + (h − y₁)⁻²)` solves `ỹ_t = h + ∫ₜᵀ ε(ỹ_s − y₁)³ ds` on every
`[t, T]` with `t > T − 1/(2ε(h − y₁)²)`, blows up as `t ↓ T − 1/(2ε(h − y₁)²)`, and this time
lies in `(0, T)` when `T > 1/(2ε(h − y₁)²)`. -/
theorem eq_A_6_solution (ε y₁ h T : ℝ) (hε : 0 < ε) (hy₁ : y₁ < h) :
    let t₀ := T - 1 / (2 * ε * (h - y₁) ^ 2)
    let yt : ℝ → ℝ := fun t => y₁ + 1 / Real.sqrt (2 * ε * (t - T) + ((h - y₁) ^ 2)⁻¹)
    (∀ t, t₀ < t → t ≤ T →
      MeasureTheory.IntegrableOn (fun s => ε * (yt s - y₁) ^ 3) (Set.Icc t T) ∧
        yt t = h + ∫ s in t..T, ε * (yt s - y₁) ^ 3) ∧
    Filter.Tendsto yt (nhdsWithin t₀ (Set.Ioi t₀)) Filter.atTop ∧
    (1 / (2 * ε * (h - y₁) ^ 2) < T → 0 < t₀ ∧ t₀ < T) := by sorry

end UnifiedFBSDE.Cubic
