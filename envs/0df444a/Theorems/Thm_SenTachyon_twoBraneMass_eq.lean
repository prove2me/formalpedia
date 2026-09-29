-- Prove2me | Theorems.Thm_SenTachyon_twoBraneMass_eq
-- name    : SenTachyon.twoBraneMass_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:31:59.321523+00:00
-- url     : https://prove2.me/theorems/f4e9cbb4-f715-4101-a81a-feef32ab60a2
-- title:
--   Eq. (9): mass of two D2-branes on the dual torus
-- statement:
--   Two D2-branes with vanishing field strength, each of tension $1/(4\pi^2\tilde g)$, wrapped on the dual torus of radii $\tilde R_1,\tilde R_2>0$ (area $4\pi^2\tilde R_1\tilde R_2$), with coupling $\tilde g>0$, have total mass
--   $$M=2\cdot\frac{1}{4\pi^2\tilde g}\cdot4\pi^2\tilde R_1\tilde R_2=\frac{2\tilde R_1\tilde R_2}{\tilde g}.$$
--
--   This is the mass of the classical minimum-energy configuration after tachyon condensation; it saturates the BPS bound.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 3, eq. (9)

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem twoBraneMass_eq (R₁t R₂t gt : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t) (hg : 0 < gt) :
    twoBraneMass R₁t R₂t gt = 2 * R₁t * R₂t / gt := by sorry
end SenTachyon
