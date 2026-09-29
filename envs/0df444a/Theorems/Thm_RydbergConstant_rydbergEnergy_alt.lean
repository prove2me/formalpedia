-- Prove2me | Theorems.Thm_RydbergConstant_rydbergEnergy_alt
-- name    : RydbergConstant.rydbergEnergy_alt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:20:26.041389+00:00
-- url     : https://prove2.me/theorems/eaed613c-4f58-44cc-827c-fc48bf969277
-- title:
--   Energy-unit expressions for $\mathrm{Ry}=hcR_\infty$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. With $\hbar=h/(2\pi)$, $\alpha=\frac{1}{4\pi\varepsilon_0}\frac{e^2}{\hbar c}$, $\lambda_e=h/(m_ec)$, $f_C=m_ec^2/h$, $\omega_C=2\pi f_C$, $a_0=4\pi\varepsilon_0\hbar^2/(e^2m_e)$ and $r_e=\frac1{4\pi\varepsilon_0}\frac{e^2}{m_ec^2}$, the Rydberg energy $\mathrm{Ry}=hcR_\infty$ equals each of
--
--   1. $\tfrac12m_ec^2\alpha^2$,
--   2. $\tfrac12\dfrac{e^4m_e}{(4\pi\varepsilon_0)^2\hbar^2}$,
--   3. $\tfrac12\dfrac{m_ec^2r_e}{a_0}$,
--   4. $\tfrac12\dfrac{hc\alpha^2}{\lambda_e}$,
--   5. $\tfrac12hf_C\alpha^2$,
--   6. $\tfrac12\hbar\omega_C\alpha^2$.
--
--   **Formalization Note** The last entry of this chain is cut off at the page margin in the supplied PDF; it is read as $\tfrac12\hbar\omega_C\alpha^2$, which follows from $\hbar\omega_C=hf_C$.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem rydbergEnergy_alt (K : Constants) :
    rydbergEnergy K = 1 / 2 * K.me * K.c ^ 2 * fineStructure K ^ 2 ∧
    rydbergEnergy K = 1 / 2 * (K.e ^ 4 * K.me / ((4 * Real.pi * K.ε0) ^ 2 * hbar K ^ 2)) ∧
    rydbergEnergy K = 1 / 2 * (K.me * K.c ^ 2 * classicalElectronRadius K / bohrRadius K) ∧
    rydbergEnergy K = 1 / 2 * (K.h * K.c * fineStructure K ^ 2 / comptonWavelength K) ∧
    rydbergEnergy K = 1 / 2 * K.h * comptonFrequency K * fineStructure K ^ 2 ∧
    rydbergEnergy K = 1 / 2 * hbar K * comptonAngularFrequency K * fineStructure K ^ 2 := by sorry

end RydbergConstant
