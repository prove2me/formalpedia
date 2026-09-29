-- Prove2me | Theorems.Thm_SpeedOfLight_kineticEnergy_unbounded
-- name    : SpeedOfLight.kineticEnergy_unbounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:14:00.148888+00:00
-- url     : https://prove2.me/theorems/b862057e-6f4a-434f-bbc7-e605dbf26639
-- title:
--   Unbounded energy below $c$: $(\gamma-1)mc^2$ exceeds every bound at some subluminal speed
-- statement:
--   Let $c > 0$, let $m > 0$ be a rest mass, and let $E$ be any energy bound. Then there is a speed $v$ with $0 < v < c$ whose relativistic kinetic energy exceeds $E$: $$E < (\gamma_c(v) - 1)\,m\,c^2 .$$ No finite amount of energy suffices to reach $c$: the energy required grows without bound already strictly below the speed of light.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics
open Filter Topology

namespace SpeedOfLight

theorem kineticEnergy_unbounded (c m : ℝ) (hc : 0 < c) (hm : 0 < m) (E : ℝ) :
    ∃ v : ℝ, 0 < v ∧ v < c ∧ E < kineticEnergy c m v := by sorry

end SpeedOfLight
