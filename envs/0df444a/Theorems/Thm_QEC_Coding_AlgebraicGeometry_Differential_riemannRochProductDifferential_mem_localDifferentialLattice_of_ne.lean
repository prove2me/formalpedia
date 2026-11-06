-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
-- name    : QEC.Coding.AlgebraicGeometry.Differential.riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:39.504393+00:00
-- url     : https://prove2.me/theorems/4a46b8fe-f1dc-4ec5-9eed-e1eb4a2ed9f0
-- title:
--   Differential: riemann Roch Product Differential mem local Differential Lattice of ne
-- statement:
--   Away from the selected place, the same product differential is regular.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueProduct.lean#L87-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueProduct.lean#L87-L115

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P Q : GlobalPlace k F) (hQP : Q ≠ P)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    riemannRochProductDifferential omega homega G P x y ∈
      localDifferentialLattice Q := by sorry
