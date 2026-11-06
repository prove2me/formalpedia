-- Prove2me | Theorems.Thm_UnivAccel_eq_18
-- name    : UnivAccel.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:21.033192+00:00
-- url     : https://prove2.me/theorems/bfccd514-cfcc-42c9-8e42-fd2d180a4ec7
-- title:
--   Eq. (18) — per-step loss $r^2(1+2h\sqrt\mu)^2/(4h^2)$ of a ball-driven implicit Euler step
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$ and $f(0) = \min f = 0$, and let $r > 0$, $h > 0$. Let $x_{1/2} = x + \frac{h}{1 + 2h\sqrt\mu}v$, $x_+ = \mathrm{Ball}^f_r(x_{1/2})$ with $\nabla f(x_+) \neq 0$ and (17), $h^2\|\nabla f(x_+)\| = r(1 + 2h\sqrt\mu)$, and $v_+ = \frac{v}{1 + 2h\sqrt\mu} + \frac{x_+ - x_{1/2}}{h}$. Expanding (15),
--   $$
--   h^2\mathcal R = \frac{h^2}{2}\big(\mu\|v_+\|^2 + \|\nabla f(x_+) + \sqrt\mu\, v_+\|^2\big) = h^2\Big\|\sqrt\mu\, v_+ + \tfrac12\nabla f(x_+)\Big\|^2 + \frac{h^2}{4}\|\nabla f(x_+)\|^2 \ge \frac{r^2(1 + 2h\sqrt\mu)^2}{4h^2},
--   $$
--   and with $H = f(x) + \frac12\|v + \sqrt\mu\, x\|^2$,
--   $$
--   H - H_+ \ge h\sqrt\mu\, H_+ + \frac{r^2(1 + 2h\sqrt\mu)^2}{4h^2}. \tag{18}
--   $$
--
--   Long steps decrease $H$ through the contraction term and short steps through the second term; this is the per-step loss behind the Monteiro–Svaiter rate.
--
--   Differences from the source: none.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2, eqs. (15), (17), (18), pp.12–13

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_IsIERun

namespace UnivAccel

/-- (18), §4.2, pp.12–13 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): the per-step loss of a ball-driven implicit Euler step. Let
`f` be differentiable and `μ`-strongly convex, `μ > 0`, `f(0) = min f = 0`, `r > 0`, `h > 0`,
`x_{1/2} = x + h/(1 + 2h√μ) v`, `x₊ = Ball^f_r(x_{1/2})` with `∇f(x₊) ≠ 0` and (17),
`h²‖∇f(x₊)‖ = r(1 + 2h√μ)`, and `v₊ = v/(1 + 2h√μ) + σ/h`, `σ = x₊ − x_{1/2}`. Expanding (15),
`h²𝓡 = h²/2 (μ‖v₊‖² + ‖∇f(x₊) + √μ v₊‖²) = h²‖√μ v₊ + ½∇f(x₊)‖² + h²/4 ‖∇f(x₊)‖² ≥ r²(1 + 2h√μ)²/(4h²)`,
and with `H = f(x) + ½‖v + √μ x‖²`, `H − H₊ ≥ h√μ H₊ + r²(1 + 2h√μ)²/(4h²)` (18). -/
theorem eq_18 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r h : ℝ)
    (x v xplus : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (hr : 0 < r) (hh : 0 < h)
    (hball : IsBallMin f (ieHalf μ h x v) r xplus) (hg : gradient f xplus ≠ 0)
    (h17 : h ^ 2 * ‖gradient f xplus‖ = r * (1 + 2 * h * Real.sqrt μ)) :
    let v' := (1 + 2 * h * Real.sqrt μ)⁻¹ • v + h⁻¹ • (xplus - ieHalf μ h x v)
    let H := f x + 1 / 2 * ‖v + Real.sqrt μ • x‖ ^ 2
    let H' := f xplus + 1 / 2 * ‖v' + Real.sqrt μ • xplus‖ ^ 2
    h ^ 2 / 2 * (μ * ‖v'‖ ^ 2 + ‖gradient f xplus + Real.sqrt μ • v'‖ ^ 2)
      = h ^ 2 * ‖Real.sqrt μ • v' + (1 / 2 : ℝ) • gradient f xplus‖ ^ 2
        + h ^ 2 / 4 * ‖gradient f xplus‖ ^ 2 ∧
    h ^ 2 * ‖Real.sqrt μ • v' + (1 / 2 : ℝ) • gradient f xplus‖ ^ 2
        + h ^ 2 / 4 * ‖gradient f xplus‖ ^ 2
      ≥ r ^ 2 * (1 + 2 * h * Real.sqrt μ) ^ 2 / (4 * h ^ 2) ∧
    H - H' ≥ h * Real.sqrt μ * H' + r ^ 2 * (1 + 2 * h * Real.sqrt μ) ^ 2 / (4 * h ^ 2) := by sorry

end UnivAccel
