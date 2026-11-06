-- Prove2me | Theorems.Thm_UnivAccel_ball_step_is_implicit_euler
-- name    : UnivAccel.ball_step_is_implicit_euler
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:31.87212+00:00
-- url     : https://prove2.me/theorems/a431b1c9-5ec2-4dba-84aa-6cc31df05b3f
-- title:
--   §4.2 — a ball step at a duration solving (17) is an implicit Euler step
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$, and let $r > 0$, $h > 0$. Set
--   $$
--   x_{1/2} = x + \frac{h}{1 + 2h\sqrt\mu}\, v, \qquad x_+ = \mathrm{Ball}^f_r(x_{1/2}), \qquad \sigma = x_+ - x_{1/2}.
--   $$
--   1. If the ball around $x_{1/2}$ contains the minimizer of $f$, the oracle returns it.
--   2. Otherwise ($\nabla f(x_+) \neq 0$) $x_+$ lies on the boundary of the ball: $\|\sigma\| = r$ and $\sigma = -t\nabla f(x_+)$ for some $t > 0$.
--   3. If moreover $h$ satisfies the implicit equation
--   $$
--   h^2\|\nabla f(x_+)\| = r(1 + 2h\sqrt\mu), \tag{17}
--   $$
--   then $\sigma = -\frac{h^2}{1 + 2h\sqrt\mu}\nabla f(x_+)$ and, with $v_+ = \frac{v}{1 + 2h\sqrt\mu} + \frac{\sigma}{h}$, the pair $(x_+, v_+)$ is the implicit Euler step (13): $x_+ - x = hv_+$, $v_+ - v = -h\nabla f(x_+) - 2h\sqrt\mu\, v_+$.
--
--   So one ball query at the right duration performs one exact implicit Euler step of the heavy-ball ODE.
--
--   Differences from the source:
--   - encoding: "σ is parallel to −∇f(x+)" → σ = −t∇f(x₊) for some t > 0; reason: the meaning of parallel with the stated orientation
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2, eqs. (13), (17), p.12

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_IsIERun

namespace UnivAccel

/-- §4.2, p.12 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): a ball step of the right duration is an implicit Euler step. Let
`f` be differentiable and `μ`-strongly convex, `μ > 0`, `r > 0`, `h > 0`, and set
`x_{1/2} = x + h/(1 + 2h√μ) v`, `x₊ = Ball^f_r(x_{1/2})` (any minimizer of `f` over the ball of radius
`r` around `x_{1/2}`) and `σ = x₊ − x_{1/2}`. If the ball contains the minimizer, the oracle returns
it. Otherwise (`∇f(x₊) ≠ 0`) `x₊` lies on the boundary, so `‖σ‖ = r` and `σ` is parallel to
`−∇f(x₊)`. If moreover `h` satisfies (17), `h²‖∇f(x₊)‖ = r(1 + 2h√μ)`, then
`σ = −h²/(1 + 2h√μ) ∇f(x₊)` and, with `v₊ = v/(1 + 2h√μ) + σ/h`, the pair `(x₊, v₊)` is the implicit
Euler step (13): `x₊ − x = h v₊`, `v₊ − v = −h∇f(x₊) − 2h√μ v₊`. -/
theorem ball_step_is_implicit_euler {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r h : ℝ)
    (x v xplus : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ) (hr : 0 < r)
    (hh : 0 < h) (hball : IsBallMin f (ieHalf μ h x v) r xplus) :
    let xh := ieHalf μ h x v
    let σ := xplus - xh
    (∀ z, (∀ y, f z ≤ f y) → z ∈ Metric.closedBall xh r → xplus = z) ∧
    (gradient f xplus ≠ 0 → ‖σ‖ = r ∧ ∃ t : ℝ, 0 < t ∧ σ = -(t • gradient f xplus)) ∧
    (gradient f xplus ≠ 0 →
      h ^ 2 * ‖gradient f xplus‖ = r * (1 + 2 * h * Real.sqrt μ) →
      let v' := (1 + 2 * h * Real.sqrt μ)⁻¹ • v + h⁻¹ • σ
      σ = -((h ^ 2 / (1 + 2 * h * Real.sqrt μ)) • gradient f xplus) ∧
      xplus - x = h • v' ∧
      v' - v = -(h • gradient f xplus) - (2 * h * Real.sqrt μ) • v') := by sorry

end UnivAccel
