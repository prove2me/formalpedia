-- Prove2me | Theorems.Thm_SpeedOfLight_velAdd_light_speed
-- name    : SpeedOfLight.velAdd_light_speed
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T12:29:09.671976+00:00
-- url     : https://prove2.me/theorems/74dd874d-0b61-4d39-9688-d5479ae408e7
-- title:
--   Light composed with any subluminal velocity still travels at $c$
-- statement:
--   Let $c > 0$ and $|v| < c$. Composing the speed $c$ with the velocity $v$ by the relativistic addition law returns $c$ again: $$c \oplus_c v = \frac{c + v}{1 + cv/c^2} = c .$$ This is the invariance of the speed of light under a change of inertial frame: an observer moving at any subluminal velocity relative to the original frame still measures light as moving at $c$.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics
open Filter Topology

namespace SpeedOfLight

theorem velAdd_light_speed (c v : ℝ) (hc : 0 < c) (hv : |v| < c) :
    velAdd c c v = c := by sorry

end SpeedOfLight
