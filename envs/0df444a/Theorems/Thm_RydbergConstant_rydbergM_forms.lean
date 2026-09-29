-- Prove2me | Theorems.Thm_RydbergConstant_rydbergM_forms
-- name    : RydbergConstant.rydbergM_forms
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:14:02.875512+00:00
-- url     : https://prove2.me/theorems/5c867a1e-57a2-4bc3-8bc7-22110f165400
-- title:
--   Reduced-mass corrected Rydberg constant: $R_M=R_\infty/(1+m_e/M)=\frac{M}{m_e+M}R_\infty$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. Let $M>0$ be the mass of the nucleus, $\mu=1/(1/m_e+1/M)$ the reduced mass and $R_M=(\mu/m_e)R_\infty$ the corrected Rydberg constant, where $R_\infty=m_ee^4/(8\varepsilon_0^2h^3c)$. Then
--
--   $$R_M=\frac{R_\infty}{1+m_e/M}\qquad\text{and}\qquad R_M=\frac{M}{m_e+M}\,R_\infty .$$
--
--   The second form with $M=m_p$ is the hydrogen value $R_{\mathrm H}$; the three forms of the correction used in the source agree.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem rydbergM_forms (K : Constants) (M : ℝ) (hM : 0 < M) :
    rydbergM K M = rydbergInf K / (1 + K.me / M) ∧
    rydbergM K M = M / (K.me + M) * rydbergInf K := by sorry

end RydbergConstant
