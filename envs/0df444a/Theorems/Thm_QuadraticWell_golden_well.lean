-- Prove2me | Theorems.Thm_QuadraticWell_golden_well
-- name    : QuadraticWell.golden_well
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T06:36:39.046624+00:00
-- url     : https://prove2.me/theorems/d64f0439-d423-454c-ac43-9b896c8e4398
-- title:
--   Corollary: the golden-ratio well is the normal form in disguise
-- statement:
--   For every twice continuously differentiable $x : \mathbb{R} \to \mathbb{R}$,
--
--   $$
--   \bigl(\forall t,\ x''(t) = -(x(t)^2 - x(t) - 1)\bigr) \iff \bigl(\forall \tau,\ z''(\tau) = -(z(\tau)^2 - 1)\bigr),
--   \qquad z(\tau) = \frac{x(\tau/\omega) - \tfrac12}{\sqrt5/2},\quad \omega = \sqrt{\sqrt5/2}.
--   $$
--
--   The well $x^2 - x - 1$ has roots $\varphi$ and $-1/\varphi$; its $\varphi$ is a choice of coordinates.
-- source:
--   Motivated by the scaling analysis in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b ; public references: Wikipedia, "Nondimensionalization": https://en.wikipedia.org/wiki/Nondimensionalization ; Wikipedia, "Golden ratio": https://en.wikipedia.org/wiki/Golden_ratio

import Mathlib

namespace QuadraticWell

theorem golden_well (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) :
    (∀ t, deriv (deriv x) t = -(x t ^ 2 - x t - 1)) ↔
    (∀ τ, deriv (deriv (fun σ => (x (σ / Real.sqrt (Real.sqrt 5 / 2)) - 1 / 2) /
        (Real.sqrt 5 / 2))) τ =
      -(((x (τ / Real.sqrt (Real.sqrt 5 / 2)) - 1 / 2) / (Real.sqrt 5 / 2)) ^ 2 - 1)) := by
  sorry

end QuadraticWell
