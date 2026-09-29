-- Prove2me | Theorems.Thm_SenTachyon_minimumMass_eq
-- name    : SenTachyon.minimumMass_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:33:40.896168+00:00
-- url     : https://prove2.me/theorems/2b355551-8cdb-4290-a84c-3341c0e2e7bd
-- title:
--   Eq. (10): the minimum mass in original variables is 2/g
-- statement:
--   Let $R_1,R_2>0$ and $g>0$. Expressing the mass (9) through the original variables using $\tilde R_i=1/R_i$ and $\tilde g=g/(R_1R_2)$ (eqs. (2), (3)) gives
--   $$M=\frac{2\tilde R_1\tilde R_2}{\tilde g}=\frac{2}{g}.$$
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 3, eq. (10)

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem minimumMass_eq (R₁ R₂ g : ℝ) (h₁ : 0 < R₁) (h₂ : 0 < R₂) (hg : 0 < g) :
    minimumMass R₁ R₂ g = 2 / g := by sorry
end SenTachyon
