-- Prove2me | Theorems.Thm_QuadraticWell_force_shift
-- name    : QuadraticWell.force_shift
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T06:19:26.811304+00:00
-- url     : https://prove2.me/theorems/1badf4c0-db62-48fa-83b1-b8ada27ecfc0
-- title:
--   The quadratic force in shifted, scaled form
-- statement:
--   Let $r_1 \neq r_2$ be real, $m = (r_1 + r_2)/2$, and $d = (r_1 - r_2)/2$ or $d = (r_2 - r_1)/2$. Then for all real $a$ and $y$,
--
--   $$
--   -a\,(y - r_1)(y - r_2) = -a\,d^2\left(\left(\frac{y - m}{d}\right)^2 - 1\right).
--   $$
-- source:
--   Motivated by the scaling analysis in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b ; public references: Wikipedia, "Nondimensionalization": https://en.wikipedia.org/wiki/Nondimensionalization ; Wikipedia, "Golden ratio": https://en.wikipedia.org/wiki/Golden_ratio

import Mathlib

namespace QuadraticWell

theorem force_shift (a r₁ r₂ d : ℝ) (hr : r₁ ≠ r₂)
    (hd : d = (r₁ - r₂) / 2 ∨ d = (r₂ - r₁) / 2) (y : ℝ) :
    -a * (y - r₁) * (y - r₂) = -a * d ^ 2 * (((y - (r₁ + r₂) / 2) / d) ^ 2 - 1) := by
  sorry

end QuadraticWell
