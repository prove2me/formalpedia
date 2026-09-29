-- Prove2me | Theorems.Thm_SpeedOfLight_boost_preserves_lorentzInterval
-- name    : SpeedOfLight.boost_preserves_lorentzInterval
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T12:25:14.870003+00:00
-- url     : https://prove2.me/theorems/d8ab7d29-ee57-4c52-943e-0d4175004213
-- title:
--   A subluminal Lorentz boost preserves the spacetime interval $c^2t^2 - x^2$
-- statement:
--   Let $c > 0$ and let $v$ be a subluminal velocity, $|v| < c$. Applying the Lorentz boost of velocity $v$ to an event with spatial coordinate $x$ and time coordinate $t$ leaves the Lorentz interval unchanged: $$c^2 (\gamma_c(v)(t - vx/c^2))^2 - (\gamma_c(v)(x - vt))^2 = c^2 t^2 - x^2 .$$ This is the statement that a boost is an isometry of the quadratic form $c^2t^2 - x^2$, and in particular that the light cone $c^2t^2 = x^2$ is the same set in every inertial frame.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics
open Filter Topology

namespace SpeedOfLight

theorem boost_preserves_lorentzInterval (c v x t : ℝ) (hc : 0 < c) (hv : |v| < c) :
    lorentzInterval c (boost c v x t).1 (boost c v x t).2 = lorentzInterval c x t := by sorry

end SpeedOfLight
