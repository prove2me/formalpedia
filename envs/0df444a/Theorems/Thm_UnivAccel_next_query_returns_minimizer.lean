-- Prove2me | Theorems.Thm_UnivAccel_next_query_returns_minimizer
-- name    : UnivAccel.next_query_returns_minimizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:02.420212+00:00
-- url     : https://prove2.me/theorems/e2501c88-3942-4cbc-be79-874e42a02bfe
-- title:
--   §5.4 — once $H \le \mu r^2/2$, the next query returns $z$
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be convex and differentiable, $\mu > 0$, $r > 0$, $h > 0$, and let $z$ minimize $\tilde f(x) = f(x) + \frac\mu2\|x - a\|^2$. Take a lookahead state $(x, \bar w)$, write $w = \bar w - \sqrt\mu\, z$ (the deviation in coordinates centred at $z$) and $H = \tilde f(x) - \tilde f(z) + \frac12\|w\|^2$, and suppose $H \le \mu r^2/2$. The predicted point $\tilde x = (x + h\bar w)/(1 + h\sqrt\mu)$ satisfies $\tilde x - z = ((x - z) + hw)/(1 + h\sqrt\mu)$ and
--   $$
--   \|\tilde x - z\|^2 \le \frac{(1/\mu + h^2)(\mu\|x - z\|^2 + \|w\|^2)}{(1 + h\sqrt\mu)^2} \le \frac{2H}{\mu} \le r^2 ,
--   $$
--   so the ball of radius $r$ around $\tilde x$ contains $z$, and every minimizer of $\tilde f$ over that ball (every valid ball-oracle answer) equals $z$.
--
--   This ends each restart phase of the lookahead method once the block potential bound falls below $\mu r^2/2$.
--
--   Differences from the source:
--   - encoding: coordinates centred at z with the deviation w → original coordinates with w = w̄ − √μ z and x̃ = laPredict μ h x w̄; reason: the paper's change of coordinates; (44) commutes with the shift x ↦ x − z, w̄ ↦ w̄ − √μ z
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.4 "Cost of a phase", p.25

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_laUpdate

namespace UnivAccel

/-- §5.4, p.25 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): once `H ≤ μr²/2`, the next query returns `z`. Let `f` be convex
and differentiable, `μ > 0`, `r > 0`, `f̃(x) = f(x) + μ/2 ‖x − a‖²` with minimizer `z`, `h > 0`, and a
lookahead state `(x, w̄)` with `w = w̄ − √μ z` (coordinates centred at `z`) and
`H = f̃(x) − f̃(z) + ½‖w‖² ≤ μr²/2`. The predicted point `x̃ = (x + h w̄)/(1 + h√μ)` satisfies
`x̃ − z = ((x − z) + hw)/(1 + h√μ)` and
`‖x̃ − z‖² ≤ (1/μ + h²)(μ‖x − z‖² + ‖w‖²)/(1 + h√μ)² ≤ 2H/μ ≤ r²`, and every minimizer of `f̃` over the
ball of radius `r` around `x̃` (every valid ball-oracle answer) is `z`. -/
theorem next_query_returns_minimizer {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r h : ℝ)
    (a z x wbar : EuclideanSpace ℝ (Fin n))
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (hμ : 0 < μ) (hr : 0 < r) (hh : 0 < h)
    (hz : ∀ y, regObj f μ a z ≤ regObj f μ a y)
    (hH : regObj f μ a x - regObj f μ a z + 1 / 2 * ‖wbar - Real.sqrt μ • z‖ ^ 2
      ≤ μ * r ^ 2 / 2) :
    let w := wbar - Real.sqrt μ • z
    let H := regObj f μ a x - regObj f μ a z + 1 / 2 * ‖w‖ ^ 2
    let xt := laPredict μ h x wbar
    xt - z = (1 + h * Real.sqrt μ)⁻¹ • ((x - z) + h • w) ∧
    ‖xt - z‖ ^ 2 ≤ (1 / μ + h ^ 2) * (μ * ‖x - z‖ ^ 2 + ‖w‖ ^ 2) / (1 + h * Real.sqrt μ) ^ 2 ∧
    (1 / μ + h ^ 2) * (μ * ‖x - z‖ ^ 2 + ‖w‖ ^ 2) / (1 + h * Real.sqrt μ) ^ 2 ≤ 2 * H / μ ∧
    2 * H / μ ≤ r ^ 2 ∧
    ∀ y, IsBallMin (regObj f μ a) xt r y → y = z := by sorry

end UnivAccel
