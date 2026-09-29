-- Prove2me | Theorems.Thm_QuadraticWell_quadratic_well_equiv
-- name    : QuadraticWell.quadratic_well_equiv
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T06:33:37.392613+00:00
-- url     : https://prove2.me/theorems/f9298e70-0c29-4f54-a448-291860e866e1
-- title:
--   Every quadratic-force oscillator is $z'' = -(z^2 - 1)$ in different units
-- statement:
--   Let $a \neq 0$ and $r_1 \neq r_2$ be real. Then there are real numbers $m$, $d$, $\omega$ with $d \neq 0$ and $\omega > 0$, chosen once, before any solution is considered, such that for every twice continuously differentiable $x : \mathbb{R} \to \mathbb{R}$:
--
--   $$
--   \bigl(\forall t,\ x''(t) = -a\,(x(t) - r_1)(x(t) - r_2)\bigr) \iff \bigl(\forall \tau,\ z''(\tau) = -(z(\tau)^2 - 1)\bigr),
--   $$
--
--   where $z(\tau) = (x(\tau/\omega) - m)/d$. (Explicitly $m = (r_1 + r_2)/2$, $d = \pm(r_1 - r_2)/2$ with $a d > 0$, and $\omega = \sqrt{a d}$.)
-- source:
--   Motivated by the scaling analysis in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b ; public references: Wikipedia, "Nondimensionalization": https://en.wikipedia.org/wiki/Nondimensionalization ; Wikipedia, "Golden ratio": https://en.wikipedia.org/wiki/Golden_ratio

import Mathlib

namespace QuadraticWell

/-- MISSION GOAL: every quadratic-force oscillator with two distinct real roots is
the normal-form oscillator z'' = -(z² - 1) after one fixed affine change of value
and one fixed rescaling of time. -/
theorem quadratic_well_equiv (a r₁ r₂ : ℝ) (ha : a ≠ 0) (hr : r₁ ≠ r₂) :
    ∃ m d ω : ℝ, d ≠ 0 ∧ 0 < ω ∧
      ∀ x : ℝ → ℝ, ContDiff ℝ 2 x →
        ((∀ t, deriv (deriv x) t = -a * (x t - r₁) * (x t - r₂)) ↔
         (∀ τ, deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ =
                -(((x (τ / ω) - m) / d) ^ 2 - 1))) := by
  sorry

end QuadraticWell
