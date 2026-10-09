-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_necessity_iii_alpha0_zero
-- name    : UnifiedFBSDE.Rational.necessity_iii_alpha0_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:05.056821+00:00
-- url     : https://prove2.me/theorems/b4fc844b-4bc5-45ff-9de5-2b991f933048
-- title:
--   Appendix, proof of Theorem 5.6 (Necessity) (iii), p. 48 (corrected) — α₀ = 0, no zero in [h, σ₃⁻¹), F's polynomial ≠ 0 at σ₃⁻¹: no (5.9) solution for large T
-- statement:
--   Let $F$ be the function (3.9) with constant coefficients, $\sigma_3\neq0$, $h<\sigma_3^{-1}$, $F(h)\ge0$, and suppose (5.8) holds with $\alpha_0=0$, so that $F(y)=p(y):=\alpha_1+\alpha_2y+\alpha_3y^2$ off the pole, where $\alpha_3=b_2-b_3\sigma_2/\sigma_3$. Assume that $F$ has no zero point in $[h,\sigma_3^{-1})$ and that
--   $$
--   p(\sigma_3^{-1})=\alpha_1+\alpha_2\sigma_3^{-1}+\alpha_3\sigma_3^{-2}\neq0 .
--   $$
--   Then there is $T_0$ such that for every $T\ge T_0$ the ODE (5.3), $y_t=h+\int_t^TF(y_s)\,ds$, has no solution on $[0,T]$ satisfying (5.9).
--
--   On the page this is the case closed by comparison with the linear function $\tilde y_t=h+\varepsilon(T-t)$, which reaches the pole in finite time.
--
--   **Formalization Note** The hypothesis $p(\sigma_3^{-1})\neq0$ is added. The page asserts that "$F$ is continuous and positive on $[h,\sigma_3^{-1}]$", which fails when the polynomial vanishes at the pole: for $\sigma_3=1$, $f_1=1$, $f_2=-1$, all other coefficients $0$ and $h=0$, $F(y)=1-y$ and $y_t=1-e^{t-T}$ satisfies (5.9) on every horizon. The added hypothesis is exactly the page's positivity at the endpoint.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 48, Appendix, proof of Theorem 5.6 (Necessity), (iii), last paragraph ("Finally, if α₀ = 0")

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Appendix, proof of Theorem 5.6 (Necessity) (iii), last case, p. 48, **corrected**: if
`h < 1/σ₃`, `F(h) ≥ 0`, the constant `α₀` of (5.8) is `0`, `F` has no zero point in
`[h, 1/σ₃)`, and the polynomial `α₁ + α₂ y + α₃ y²` (which equals `F` off the pole) does not
vanish at `y = 1/σ₃`, then for all large `T` the ODE (5.3) has no solution satisfying (5.9).
The last hypothesis is the page's claim "F is continuous and positive on `[h, σ₃⁻¹]`"; without
it the statement is false (e.g. `F(y) = 1 − y`, `σ₃ = 1`, `h = 0`). -/
theorem necessity_iii_alpha0_zero (c : Coeffs) (h α₁ α₂ : ℝ) (hσ : c.σ₃ ≠ 0)
    (hh : h < 1 / c.σ₃) (hFh : 0 ≤ c.F h) (hdec : c.IsDecomp58 0 α₁ α₂)
    (hpole : α₁ + α₂ * (1 / c.σ₃) + c.α₃ * (1 / c.σ₃) ^ 2 ≠ 0)
    (hnz : ∀ y : ℝ, h ≤ y → y < 1 / c.σ₃ → c.F y ≠ 0) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ¬ ∃ y : ℝ → ℝ, IsSolution59 c h T y := by sorry

end UnifiedFBSDE.Rational
