-- Prove2me | Theorems.Thm_SpeedOfLight_speed_of_light_invariant_and_unattainable
-- name    : SpeedOfLight.speed_of_light_invariant_and_unattainable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:22:19.168566+00:00
-- url     : https://prove2.me/theorems/7cbffcca-ea52-4f6c-bd5c-afb6bbf80c0f
-- title:
--   $c$ is an invariant and unattainable speed limit
-- statement:
--   The goal of the mission. For every invariant speed $c > 0$ and every rest mass $m > 0$:
--
--   1. *(Invariance)* composing $c$ with any subluminal velocity $v$, $|v| < c$, again gives $c$, so light has the same speed in every inertial frame;
--   2. *(Speed limit)* any two subluminal velocities compose to a subluminal velocity, so $c$ is never reached by composing boosts;
--   3. *(Unattainability)* for every energy bound $E$ there is a speed strictly between $0$ and $c$ whose relativistic kinetic energy $(\gamma_c(v)-1)mc^2$ exceeds $E$, so accelerating a massive body to $c$ would require unbounded energy.
--
--   Together these formalize the two claims the source material makes about $c$: that it is the same for all observers, and that it is an upper limit that massive particles can approach but never reach.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics
open Filter Topology

namespace SpeedOfLight

theorem speed_of_light_invariant_and_unattainable (c m : ℝ) (hc : 0 < c) (hm : 0 < m) :
    (∀ v : ℝ, |v| < c → velAdd c c v = c) ∧
    (∀ u v : ℝ, |u| < c → |v| < c → |velAdd c u v| < c) ∧
    (∀ E : ℝ, ∃ v : ℝ, 0 < v ∧ v < c ∧ E < kineticEnergy c m v) := by sorry

end SpeedOfLight
