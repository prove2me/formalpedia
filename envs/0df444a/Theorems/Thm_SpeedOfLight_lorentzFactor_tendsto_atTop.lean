-- Prove2me | Theorems.Thm_SpeedOfLight_lorentzFactor_tendsto_atTop
-- name    : SpeedOfLight.lorentzFactor_tendsto_atTop
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:10:59.936916+00:00
-- url     : https://prove2.me/theorems/a0657e23-62f2-4bae-8f7a-ece916b86047
-- title:
--   The Lorentz factor diverges as $v \to c^{-}$
-- statement:
--   Let $c > 0$. As the speed $v$ increases to $c$ from below, the Lorentz factor $\gamma_c(v) = 1/\sqrt{1 - v^2/c^2}$ tends to $+\infty$: for every bound $M$ there is a left neighbourhood of $c$ on which $\gamma_c > M$. The limit is taken along the one-sided filter of speeds strictly below $c$, which is the only regime in which $\gamma_c$ has its intended meaning.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics
open Filter Topology

namespace SpeedOfLight

theorem lorentzFactor_tendsto_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (lorentzFactor c) (𝓝[<] c) atTop := by sorry

end SpeedOfLight
