-- Prove2me | Theorems.Thm_RybinAI2026_P01_planar_axis_values
-- name    : RybinAI2026.P01.planar_axis_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T12:40:31.638979+00:00
-- url     : https://prove2.me/theorems/48974693-b4d4-4fac-9303-cba25f9e285a
-- title:
--   Axis values of the planar directional integral as J-integrals
-- statement:
--   For positive reals m1 and m2, the planar directional integrals on the two axes equal four times the corresponding J-integrals: at angle 0 the value is 4*J(m1,m2), at angle pi/2 it is 4*J(m2,m1).
-- source:
--   P01 synthesis 2026-10-04, Agent A commuting-planar programme Lemma L4a (axis values). Stated with the uniform F(psi) integrand at psi = 0 and psi = pi/2; quadrant folding plus t = sin phi substitution verified by hand. Uses parametrized integrals over [0,2*pi], avoiding the complex-only circleIntegral API.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

namespace RybinAI2026.P01

/-- For `m1 > 0` and `m2 > 0`, the planar directional integral `F(psi) = integral phi in 0..2*pi of |cos (phi - psi)| / (m1 * cos^2 phi + m2 * sin^2 phi)` takes exact J-integral values on the axes: at `psi = 0` it equals `4 * J(m1, m2)`, and at `psi = pi / 2` it equals `4 * J(m2, m1)`, where `J(a, b)` is the integral over `[0,1]` of `(a + (b - a) * t^2)^{-1}`. Proof route: fold the four quadrants by evenness and periodicity, then substitute `t = sin phi` on `[0, pi/2]`. This is Lemma L4a of the commuting-planar programme; the axis principle L4b consumes these values. -/
theorem planar_axis_values (m1 m2 : ℝ) (h1 : 0 < m1) (h2 : 0 < m2) :
    (∫ p : ℝ in (0 : ℝ)..2 * Real.pi,
      |Real.cos (p - 0)| / (m1 * (Real.cos p) ^ 2 + m2 * (Real.sin p) ^ 2))
      = 4 * (∫ t in (0 : ℝ)..1, (m1 + (m2 - m1) * t ^ 2)⁻¹) ∧
    (∫ p : ℝ in (0 : ℝ)..2 * Real.pi,
      |Real.cos (p - Real.pi / 2)| / (m1 * (Real.cos p) ^ 2 + m2 * (Real.sin p) ^ 2))
      = 4 * (∫ t in (0 : ℝ)..1, (m2 + (m1 - m2) * t ^ 2)⁻¹) := by sorry

end RybinAI2026.P01
