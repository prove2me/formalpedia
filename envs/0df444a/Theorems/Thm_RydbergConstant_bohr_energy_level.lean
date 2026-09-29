-- Prove2me | Theorems.Thm_RydbergConstant_bohr_energy_level
-- name    : RydbergConstant.bohr_energy_level
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:24:40.359812+00:00
-- url     : https://prove2.me/theorems/0669f12f-464a-4bb9-86b3-be691272f04c
-- title:
--   Bohr energy levels (infinite nuclear mass): $E_n=-hcR_\infty/n^2$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. Let $n\ge1$ and suppose an electron of mass $m_e$ and charge $-e$ moves on a circular Bohr orbit of radius $r>0$ with speed $v>0$ about a fixed (infinitely heavy) charge $+e$:
--
--   $$\frac{m_ev^2}{r}=\frac{e^2}{4\pi\varepsilon_0r^2},\qquad m_evr=n\hbar,\qquad \hbar=\frac h{2\pi}.$$
--
--   Then its energy $E=\tfrac12m_ev^2-\dfrac{e^2}{4\pi\varepsilon_0r}$ is
--
--   $$E=-\frac{hcR_\infty}{n^2},\qquad R_\infty=\frac{m_ee^4}{8\varepsilon_0^2h^3c}.$$
--
--   This identifies the Rydberg energy as the coefficient of the hydrogen energy levels in the Bohr model.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem bohr_energy_level (K : Constants) (n : ℕ) (hn : 0 < n) (r v : ℝ)
    (horb : IsBohrOrbit K K.me n r v) :
    orbitEnergy K K.me r v = -rydbergEnergy K / (n : ℝ) ^ 2 := by sorry

end RydbergConstant
