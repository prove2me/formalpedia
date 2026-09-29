-- Prove2me | Theorems.Thm_SenTachyon_minimumEnergyDensity_eq
-- name    : SenTachyon.minimumEnergyDensity_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:35:43.617046+00:00
-- url     : https://prove2.me/theorems/4c34d74f-fa29-424a-b616-06869abc0573
-- title:
--   Eq. (11): energy per unit area at the tachyon minimum
-- statement:
--   Let $R_1,R_2>0$ and $g>0$. At the minimum of the tachyon potential, the energy per unit area of the brane–antibrane system on the torus of area $4\pi^2R_1R_2$ is
--   $$\frac{M}{4\pi^2R_1R_2}=\frac{1}{2\pi^2R_1R_2\,g}.$$
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 3, eq. (11)

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem minimumEnergyDensity_eq (R₁ R₂ g : ℝ) (h₁ : 0 < R₁) (h₂ : 0 < R₂) (hg : 0 < g) :
    minimumEnergyDensity R₁ R₂ g = 1 / (2 * Real.pi ^ 2 * R₁ * R₂ * g) := by sorry
end SenTachyon
