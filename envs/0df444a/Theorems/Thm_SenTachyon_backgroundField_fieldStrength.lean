-- Prove2me | Theorems.Thm_SenTachyon_backgroundField_fieldStrength
-- name    : SenTachyon.backgroundField_fieldStrength
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:19:36.4805+00:00
-- url     : https://prove2.me/theorems/223785c8-d98e-4777-8127-bd4f9a877dd4
-- title:
--   Field strength of the background (4) is (2π/Ṽ)σ₃
-- statement:
--   Let $\tilde R_1,\tilde R_2>0$, $\tilde V=4\pi^2\tilde R_1\tilde R_2$, and let $A$ be the background field (4). Its field strength $F_{12}=\partial_1A_2-\partial_2A_1-i[A_1,A_2]$ is constant and non-zero:
--   $$F_{12}(x)=\frac{2\pi}{\tilde V}\,\sigma_3\quad\text{for all }x .$$
--
--   This is the non-vanishing field strength, hence positive energy density, of the configuration (4) referred to after eq. (7): $\pm1$ unit of flux on the two diagonal $U(1)$ factors.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 2, paragraph after eq. (7) ("gives rise to a non-vanishing field strength")

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem backgroundField_fieldStrength (R₁t R₂t : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t)
    (x : ℝ × ℝ) :
    fieldStrength (backgroundField R₁t R₂t) x
      = ((2 * Real.pi / torusArea R₁t R₂t : ℝ) : ℂ) • pauli3 := by sorry
end SenTachyon
