-- Prove2me | Theorems.Thm_QuadraticWell_rescale_deriv2
-- name    : QuadraticWell.rescale_deriv2
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T06:28:17.306684+00:00
-- url     : https://prove2.me/theorems/f9cb46ce-a156-491c-b04f-8992c43357e4
-- title:
--   Chain rule for the rescaling: $z''(\tau) = x''(\tau/\omega)/(\omega^2 d)$
-- statement:
--   Let $x : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable, $m$ real, and $\omega, d$ real and nonzero. Then for every $\tau$, the function $z(\sigma) = (x(\sigma/\omega) - m)/d$ satisfies
--
--   $$
--   z''(\tau) = \frac{x''(\tau/\omega)}{\omega^2\, d}.
--   $$
-- source:
--   Motivated by the scaling analysis in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b ; public references: Wikipedia, "Nondimensionalization": https://en.wikipedia.org/wiki/Nondimensionalization ; Wikipedia, "Golden ratio": https://en.wikipedia.org/wiki/Golden_ratio

import Mathlib

namespace QuadraticWell

theorem rescale_deriv2 (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) (m d ω : ℝ) (hω : ω ≠ 0)
    (hd : d ≠ 0) (τ : ℝ) :
    deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ = deriv (deriv x) (τ / ω) / (ω ^ 2 * d) := by
  sorry

end QuadraticWell
