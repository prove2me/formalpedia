-- Prove2me | Theorems.Thm_SpeedOfLight_velAdd_lt_light_speed
-- name    : SpeedOfLight.velAdd_lt_light_speed
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T12:43:57.554768+00:00
-- url     : https://prove2.me/theorems/4d168675-2d8b-4831-93bf-04298d10c6b2
-- title:
--   Subluminal speeds are closed under relativistic velocity addition
-- statement:
--   Let $c > 0$ and let $u, v$ be speeds with $|u| < c$ and $|v| < c$. Then their relativistic sum is again strictly subluminal: $$\left| \frac{u+v}{1 + uv/c^2} \right| < c .$$ Hence no finite chain of subluminal boosts ever attains the speed $c$; the open interval $(-c, c)$ is closed under $\oplus_c$. The inequality is strict on both sides, and the conclusion is stated for the absolute value, so it covers velocities of either sign.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics
open Filter Topology

namespace SpeedOfLight

theorem velAdd_lt_light_speed (c u v : ℝ) (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) :
    |velAdd c u v| < c := by sorry

end SpeedOfLight
