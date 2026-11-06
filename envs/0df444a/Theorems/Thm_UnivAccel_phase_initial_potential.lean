-- Prove2me | Theorems.Thm_UnivAccel_phase_initial_potential
-- name    : UnivAccel.phase_initial_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:52.580274+00:00
-- url     : https://prove2.me/theorems/5c513249-f8a1-4c35-ac8b-411598482444
-- title:
--   §5.4 Cost of a phase — $H_0 \le 2(\tilde f(a)-\tilde f(z)) \le 2\mu R^2$
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be convex and differentiable with minimizer $x^*$, let $\mu > 0$, and let $z$ minimize $\tilde f(x) = f(x) + \frac\mu2\|x - a\|^2$. Consider the phase potential $H = \tilde f(x) - \tilde f(z) + \frac12\|w\|^2$ with $w = v + \sqrt\mu(x - z)$, at the start of the phase ($x = a$, $v = 0$). Then strong convexity of $\tilde f$ gives $\frac\mu2\|a - z\|^2 \le \tilde f(a) - \tilde f(z)$, and
--   $$
--   H_0 = \tilde f(a) - \tilde f(z) + \frac12\|\sqrt\mu(a - z)\|^2 \le 2\big(\tilde f(a) - \tilde f(z)\big) \le 2\big(f(a) - f(x^*)\big),
--   $$
--   which equals $2\mu R^2$ when $\mu = (f(a) - f(x^*))/R^2$.
--
--   This is the initial-energy bound each restart phase needs before the block analysis of §5.3 applies.
--
--   Differences from the source:
--   - generalization: x* = 0, f(x*) = 0, μ = f(a)/R², so H0 ≤ 2f(a) = 2μR² → any minimizer x* and μ > 0: H0 ≤ 2(f̃(a) − f̃(z)) ≤ 2(f(a) − f(x*)), equal to 2μR² when μ = (f(a) − f(x*))/R²; reason: translating x* to 0 gives the printed chain; the restart with the gap bound Δ_k needs the general form
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.4 "Cost of a phase", p.24

import Mathlib
import Definitions.Def_UnivAccel_regObj

namespace UnivAccel

/-- §5.4 "Cost of a phase", p.24 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): the initial potential of a phase is at most
`2μR²`. Let `f` be convex and differentiable with minimizer `x*`, `μ > 0`, `z = arg min f̃` for
`f̃(x) = f(x) + μ/2 ‖x − a‖²`, and `H = f̃(x) − f̃(z) + ½‖w‖²` with `w = v + √μ(x − z)`. At the start
of the phase `x = a`, `v = 0`, and strong convexity of `f̃` gives `μ/2 ‖a − z‖² ≤ f̃(a) − f̃(z)`, so
`H₀ ≤ 2(f̃(a) − f̃(z)) ≤ 2(f(a) − f(x*))`, which is `2μR²` when `μ = (f(a) − f(x*))/R²` (the page's
`μ = f(a)/R²`).

**Formalization Note** The page normalizes `x* = 0`, `f(x*) = 0`; here the minimizer is general,
and the start's `w = 0 + √μ(a − z)` is written `√μ • (a − z)`. -/
theorem phase_initial_potential {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (xstar a z : EuclideanSpace ℝ (Fin n))
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) (hmin : ∀ y, f xstar ≤ f y)
    (hμ : 0 < μ) (hz : ∀ y, regObj f μ a z ≤ regObj f μ a y) :
    μ / 2 * ‖a - z‖ ^ 2 ≤ regObj f μ a a - regObj f μ a z ∧
    regObj f μ a a - regObj f μ a z + 1 / 2 * ‖Real.sqrt μ • (a - z)‖ ^ 2
      ≤ 2 * (regObj f μ a a - regObj f μ a z) ∧
    2 * (regObj f μ a a - regObj f μ a z) ≤ 2 * (f a - f xstar) ∧
    (∀ R : ℝ, 0 < R → μ = (f a - f xstar) / R ^ 2 → 2 * (f a - f xstar) = 2 * μ * R ^ 2) := by sorry

end UnivAccel
