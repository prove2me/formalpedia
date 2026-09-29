-- Prove2me | Theorems.Thm_SenTachyon_unitFluxField_tendsto_zero
-- name    : SenTachyon.unitFluxField_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T18:47:31.371984+00:00
-- url     : https://prove2.me/theorems/e1c01f32-8709-405f-ac8f-98ec35385e6c
-- title:
--   Eq. (1): the unit-flux magnetic field vanishes on a large torus
-- statement:
--   The magnetic field carrying one unit of flux on a torus of radii $R_1,R_2$ is $F_{12}=2\pi/V$ with $V=4\pi^2R_1R_2$. It tends to zero as the torus becomes large:
--   $$\lim_{R_1,R_2\to\infty}\frac{2\pi}{4\pi^2R_1R_2}=0 .$$
--
--   This justifies recovering the flux-free brane–antibrane system in the limit $R_1,R_2\to\infty$.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 1, eq. (1) and the sentence following it

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem unitFluxField_tendsto_zero :
    Tendsto (fun R : ℝ × ℝ => unitFluxField R.1 R.2) (atTop ×ˢ atTop) (𝓝 0) := by sorry
end SenTachyon
