-- Prove2me | Theorems.Thm_QuadraticWell_sign_choice
-- name    : QuadraticWell.sign_choice
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T06:24:45.126723+00:00
-- url     : https://prove2.me/theorems/544babcc-b14a-4335-9f65-7e2307be6def
-- title:
--   The sign of $d$ can be chosen so that $a d > 0$
-- statement:
--   Let $a \neq 0$ and $r_1 \neq r_2$ be real. Then
--
--   $$
--   a\,\frac{r_1 - r_2}{2} > 0 \qquad\text{or}\qquad a\,\frac{r_2 - r_1}{2} > 0 ,
--   $$
--
--   so for one choice of $d = \pm(r_1 - r_2)/2$ the time scale $\omega = \sqrt{a d}$ is real and positive.
-- source:
--   Motivated by the scaling analysis in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b ; public references: Wikipedia, "Nondimensionalization": https://en.wikipedia.org/wiki/Nondimensionalization ; Wikipedia, "Golden ratio": https://en.wikipedia.org/wiki/Golden_ratio

import Mathlib

namespace QuadraticWell

theorem sign_choice (a r₁ r₂ : ℝ) (ha : a ≠ 0) (hr : r₁ ≠ r₂) :
    0 < a * ((r₁ - r₂) / 2) ∨ 0 < a * ((r₂ - r₁) / 2) := by
  sorry

end QuadraticWell
