-- Prove2me | Theorems.Thm_TeleparallelGravity_fieldStrength_eq_tetrad_mul_torsion
-- name    : TeleparallelGravity.fieldStrength_eq_tetrad_mul_torsion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T22:36:24.155707+00:00
-- url     : https://prove2.me/theorems/e7a286aa-7db9-460b-8202-0e29201c42a4
-- title:
--   Field strength equals tetrad-contracted torsion, $F^a{}_{\mu\nu}=h^a{}_\rho T^\rho{}_{\mu\nu}$ (Eq. (7))
-- statement:
--   Let $x^a$ and $B^a{}_\mu$ be smooth real functions on $\mathbb R^4$ such that the tetrad $h^a{}_\mu=\partial_\mu x^a+B^a{}_\mu$ is an invertible matrix at every point. Then for all $a,\mu,\nu$ and every point,
--   $$F^a{}_{\mu\nu}\equiv\partial_\mu B^a{}_\nu-\partial_\nu B^a{}_\mu=h^a{}_\rho\,T^\rho{}_{\mu\nu},$$
--   where $T^\rho{}_{\mu\nu}=\Gamma^\rho{}_{\nu\mu}-\Gamma^\rho{}_{\mu\nu}$ is the torsion of the Weitzenböck connection $\Gamma^\rho{}_{\mu\nu}=h_a{}^\rho\partial_\nu h^a{}_\mu$ of this tetrad.
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009 — Field strength equals tetrad-contracted torsion, $F^a{}_{\mu\nu}=h^a{}_\rho T^\rho{}_{\mu\nu}$ (Eq. (7))

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

open scoped ContDiff

namespace TeleparallelGravity
theorem fieldStrength_eq_tetrad_mul_torsion
    (xa : Fin 4 → Spacetime → ℝ) (B : TetradField)
    (hxa : ∀ a, ContDiff ℝ ∞ (xa a)) (hB : ∀ a μ, ContDiff ℝ ∞ (B a μ))
    (hnd : ∀ x, (tetradMatrix (tetradOfPotential xa B) x).det ≠ 0)
    (a μ ν : Fin 4) (x : Spacetime) :
    fieldStrength B a μ ν x =
      ∑ ρ, tetradOfPotential xa B a ρ x * torsion (tetradOfPotential xa B) ρ μ ν x := by
  sorry
end TeleparallelGravity
