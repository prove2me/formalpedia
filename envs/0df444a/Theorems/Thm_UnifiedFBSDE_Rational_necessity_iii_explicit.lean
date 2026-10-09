-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_necessity_iii_explicit
-- name    : UnifiedFBSDE.Rational.necessity_iii_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:03.602646+00:00
-- url     : https://prove2.me/theorems/e1d6e09f-dcdf-4096-86ab-413c9b797615
-- title:
--   Appendix, proof of Theorem 5.6 (Necessity) (iii), pp. 47–48 — comparison with (σ₃⁻¹ − ỹ_t)² = (σ₃⁻¹ − h)² − 2ε(T − t): (1 − σ₃y)⁻¹ blows up
-- statement:
--   Let $\varepsilon>0$, $h<a$, and $T\ge(a-h)^2/(2\varepsilon)$. Let $G$ be continuous on $(-\infty,a)$ and satisfy
--   $$
--   G(y)\ge\frac{\varepsilon}{a-y}\qquad\text{for }y\in[h,a).
--   $$
--   Then there is no solution of $y_t=h+\int_t^TG(y_s)\,ds$ on $[0,T]$ with $y_t<a$ for all $t\in[0,T]$ and $a-y_t\ge\kappa$ for some $\kappa>0$.
--
--   The comparison equation $\tilde y_t=h+\int_t^T\varepsilon(a-\tilde y_s)^{-1}ds$ has the explicit solution $(a-\tilde y_t)^2=(a-h)^2-2\varepsilon(T-t)$, which reaches $a$ at $t=T-(a-h)^2/(2\varepsilon)$. Applied with $a=\sigma_3^{-1}$ and $G=F$ (continuous below the pole), it shows that $(1-\sigma_3y)^{-1}$ blows up for large $T$ in the case $\alpha_0>0$.
--
--   **Formalization Note** The statement is phrased for a general continuous $G$; the page applies it to $F$. Continuity of $G$ on $(-\infty,a)$ is assumed because the comparison needs the solution to be differentiable while it stays below $a$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 47–48, Appendix, proof of Theorem 5.6 (Necessity), (iii), third paragraph ("Let ỹ solve the following ODE")

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Appendix, proof of Theorem 5.6 (Necessity) (iii), pp. 47–48: comparison with the explicit
solution `(a − ỹ_t)² = (a − h)² − 2ε(T − t)` of `ỹ_t = h + ∫ₜᵀ ε (a − ỹ_s)⁻¹ ds`
(`a = σ₃⁻¹`). If `G` is continuous on `(−∞, a)` with `G(y) ≥ ε (a − y)⁻¹` on `[h, a)` and
`T ≥ (a − h)²/(2ε)`, then no solution of `y_t = h + ∫ₜᵀ G(y_s) ds` on `[0, T]` stays below `a`
with `a − y` bounded away from `0`: `(1 − σ₃ y)⁻¹` would blow up. -/
theorem necessity_iii_explicit (G : ℝ → ℝ) (ε a h T : ℝ) (hε : 0 < ε) (hha : h < a)
    (hT : (a - h) ^ 2 / (2 * ε) ≤ T) (hG : ContinuousOn G (Set.Iio a))
    (hGb : ∀ y : ℝ, h ≤ y → y < a → ε * (a - y)⁻¹ ≤ G y) :
    ¬ ∃ y : ℝ → ℝ, UnifiedFBSDE.Cubic.IsSolution (fun _ z => G z) h T y ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, y t < a) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, κ ≤ a - y t := by sorry

end UnifiedFBSDE.Rational
