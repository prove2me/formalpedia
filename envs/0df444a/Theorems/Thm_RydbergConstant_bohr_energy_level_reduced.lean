-- Prove2me | Theorems.Thm_RydbergConstant_bohr_energy_level_reduced
-- name    : RydbergConstant.bohr_energy_level_reduced
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:30:56.775483+00:00
-- url     : https://prove2.me/theorems/963ea329-2709-4a5c-a0ee-7132137d5356
-- title:
--   Bohr energy levels with reduced mass: $E_n=-hcR_M/n^2$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. Let $M>0$ be the nuclear mass, $\mu=1/(1/m_e+1/M)$ the reduced mass and $R_M=(\mu/m_e)R_\infty$. Let $n\ge1$ and let $r>0$, $v>0$ satisfy the Bohr-orbit conditions for mass $\mu$:
--
--   $$\frac{\mu v^2}{r}=\frac{e^2}{4\pi\varepsilon_0r^2},\qquad \mu vr=n\hbar .$$
--
--   Then the orbit energy $E=\tfrac12\mu v^2-\dfrac{e^2}{4\pi\varepsilon_0r}$ equals
--
--   $$E=-\frac{hcR_M}{n^2}.$$
--
--   **Formalization Note** The source says only that the corrected formula "comes from substituting the reduced mass of the electron"; this milestone records that substitution at the level of energy levels.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem bohr_energy_level_reduced (K : Constants) (M : ℝ) (hM : 0 < M)
    (n : ℕ) (hn : 0 < n) (r v : ℝ) (horb : IsBohrOrbit K (reducedMass K M) n r v) :
    orbitEnergy K (reducedMass K M) r v = -(K.h * K.c * rydbergM K M) / (n : ℝ) ^ 2 := by sorry

end RydbergConstant
