-- Prove2me | Theorems.Thm_RydbergConstant_rydbergInf_alt
-- name    : RydbergConstant.rydbergInf_alt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:19:56.512291+00:00
-- url     : https://prove2.me/theorems/f7443ddc-c176-4abe-8bec-c6ae8d03bf0f
-- title:
--   Alternative expressions: $R_\infty=\frac{\alpha^2m_ec}{2h}=\frac{\alpha^2}{2\lambda_e}=\frac{\alpha}{4\pi a_0}$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. With $\hbar=h/(2\pi)$, $\alpha=\frac{1}{4\pi\varepsilon_0}\frac{e^2}{\hbar c}$, $\lambda_e=h/(m_ec)$ and $a_0=4\pi\varepsilon_0\hbar^2/(e^2m_e)$, the Rydberg constant $R_\infty=m_ee^4/(8\varepsilon_0^2h^3c)$ satisfies
--
--   1. $R_\infty=\dfrac{\alpha^2m_ec}{2h}$,
--   2. $R_\infty=\dfrac{\alpha^2}{2\lambda_e}$,
--   3. $R_\infty=\dfrac{\alpha}{4\pi a_0}$,
--   4. $\dfrac1{R_\infty}=\dfrac{4\pi}{\alpha}\,a_0$.
--
--   Item 4 is the source's remark that the ionizing wavelength of hydrogen is $4\pi/\alpha$ Bohr radii.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem rydbergInf_alt (K : Constants) :
    rydbergInf K = fineStructure K ^ 2 * K.me * K.c / (2 * K.h) ∧
    rydbergInf K = fineStructure K ^ 2 / (2 * comptonWavelength K) ∧
    rydbergInf K = fineStructure K / (4 * Real.pi * bohrRadius K) ∧
    1 / rydbergInf K = 4 * Real.pi / fineStructure K * bohrRadius K := by sorry

end RydbergConstant
