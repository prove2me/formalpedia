-- Prove2me | Theorems.Thm_RydbergConstant_isotopic_shift
-- name    : RydbergConstant.isotopic_shift
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:15:17.817616+00:00
-- url     : https://prove2.me/theorems/95bb2597-9216-43b5-98b6-01645875d4d5
-- title:
--   Isotopic shift: $R_M$ strictly increases with $M$ and $R_M<R_\infty$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. Let $0<M_1<M_2$ be two nuclear masses and $R_M=(\mu(M)/m_e)R_\infty$ the reduced-mass corrected Rydberg constant. Then
--
--   $$R_{M_1}<R_{M_2}<R_\infty .$$
--
--   Distinct isotopes therefore have distinct Rydberg constants (e.g. $R_{\mathrm H}<R_{\mathrm D}$), which is the isotopic shift of spectral lines; every finite-mass value lies strictly below the infinite-mass value.
--
--   **Formalization Note** The source states the shift qualitatively; the strict monotonicity in $M$ together with the bound by $R_\infty$ is the precise content formalized here.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem isotopic_shift (K : Constants) (M₁ M₂ : ℝ) (h₁ : 0 < M₁) (h₁₂ : M₁ < M₂) :
    rydbergM K M₁ < rydbergM K M₂ ∧ rydbergM K M₂ < rydbergInf K := by sorry

end RydbergConstant
