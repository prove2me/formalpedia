-- Prove2me | Theorems.Thm_RydbergConstant_rydbergEnergy_eq_alpha
-- name    : RydbergConstant.rydbergEnergy_eq_alpha
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:18:07.516959+00:00
-- url     : https://prove2.me/theorems/255f16ee-30b5-4c8f-8669-126b91692af1
-- title:
--   Rydberg unit of energy: $hcR_\infty=\alpha^2m_ec^2/2$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. With $R_\infty=m_ee^4/(8\varepsilon_0^2h^3c)$, $\hbar=h/(2\pi)$ and the fine-structure constant $\alpha=\frac{1}{4\pi\varepsilon_0}\frac{e^2}{\hbar c}$, the Rydberg unit of energy $\mathrm{Ry}=hcR_\infty$ satisfies
--
--   $$\mathrm{Ry}=hcR_\infty=\frac{\alpha^2m_ec^2}{2}.$$
--
--   This expresses the ionization energy of hydrogen in the simplified Bohr model as $\alpha^2/2$ times the electron rest energy.
--
--   **Formalization Note** The CODATA numerical values in joules and electronvolts are not formalized.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem rydbergEnergy_eq_alpha (K : Constants) :
    rydbergEnergy K = fineStructure K ^ 2 * K.me * K.c ^ 2 / 2 := by sorry

end RydbergConstant
