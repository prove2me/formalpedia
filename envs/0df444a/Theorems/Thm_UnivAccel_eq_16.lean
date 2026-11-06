-- Prove2me | Theorems.Thm_UnivAccel_eq_16
-- name    : UnivAccel.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:08.879239+00:00
-- url     : https://prove2.me/theorems/27496986-961c-4ee7-b94c-6786e0fe1cb6
-- title:
--   Eqs. (15)–(16) — implicit Euler contracts the potential, $(1+h\sqrt\mu)H_+ \le H$, for every $h$
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$ and $f(0) = \min f = 0$, and let $h > 0$. Let $(x_+, v_+)$ be an implicit Euler step (13) of the heavy-ball ODE from $(x, v)$:
--   $$
--   x_+ - x = h v_+, \qquad v_+ - v = -h\nabla f(x_+) - 2h\sqrt\mu\, v_+ .
--   $$
--   With $w = v + \sqrt\mu\, x$, $H = f(x) + \frac12\|w\|^2$ and the discretization term
--   $$
--   h^2\mathcal R := \frac\mu2\|x_+ - x\|^2 + \frac12\|\Delta w\|^2 = \frac{h^2}{2}\big(\mu\|v_+\|^2 + \|\nabla f(x_+) + \sqrt\mu\, v_+\|^2\big), \tag{15}
--   $$
--   one has
--   $$
--   H - H_+ \ge h\sqrt\mu\, H_+ + \frac{h\sqrt\mu}{2}\|v_+\|^2 + h^2\mathcal R, \qquad\text{hence}\qquad (1 + h\sqrt\mu)\, H_+ \le H. \tag{16}
--   $$
--
--   Implicit Euler thus keeps the accelerated contraction of the continuous heavy-ball dynamics with no restriction on the step size.
--
--   Differences from the source: none.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.1, eqs. (13), (15), (16), pp.10–12

import Mathlib

namespace UnivAccel

/-- (15)–(16), §4.1, pp.11–12 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): implicit Euler contracts the potential for every
step size. Let `f` be differentiable and `μ`-strongly convex, `μ > 0`, `f(0) = min f = 0`, `h > 0`,
and let `(x₊, v₊)` solve the implicit Euler step (13) from `(x, v)`:
`x₊ − x = h v₊`, `v₊ − v = −h∇f(x₊) − 2h√μ v₊`. With `w = v + √μ x`, `H = f(x) + ½‖w‖²`, and the
discretization term
`h²𝓡 := μ/2 ‖x₊ − x‖² + ½‖Δw‖² = h²/2 (μ‖v₊‖² + ‖∇f(x₊) + √μ v₊‖²)` (15),
`H − H₊ ≥ h√μ H₊ + (h√μ/2)‖v₊‖² + h²𝓡`, and hence `(1 + h√μ) H₊ ≤ H` (16). -/
theorem eq_16 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ h : ℝ)
    (x v x' v' : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (hh : 0 < h)
    (h13x : x' - x = h • v')
    (h13v : v' - v = -(h • gradient f x') - (2 * h * Real.sqrt μ) • v') :
    let H := f x + 1 / 2 * ‖v + Real.sqrt μ • x‖ ^ 2
    let H' := f x' + 1 / 2 * ‖v' + Real.sqrt μ • x'‖ ^ 2
    let hR := h ^ 2 / 2 * (μ * ‖v'‖ ^ 2 + ‖gradient f x' + Real.sqrt μ • v'‖ ^ 2)
    μ / 2 * ‖x' - x‖ ^ 2 + 1 / 2 * ‖(v' + Real.sqrt μ • x') - (v + Real.sqrt μ • x)‖ ^ 2 = hR ∧
    H - H' ≥ h * Real.sqrt μ * H' + h * Real.sqrt μ / 2 * ‖v'‖ ^ 2 + hR ∧
    (1 + h * Real.sqrt μ) * H' ≤ H := by sorry

end UnivAccel
