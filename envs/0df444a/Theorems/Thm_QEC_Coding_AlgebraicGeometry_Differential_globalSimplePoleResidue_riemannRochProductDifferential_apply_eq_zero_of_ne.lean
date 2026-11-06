-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero_of_ne
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:22.37297+00:00
-- url     : https://prove2.me/theorems/bc0ef701-cd8e-49f6-a9ee-b2b392770bda
-- title:
--   Differential: global Simple Pole Residue riemann Roch Product Differential apply eq zero of ne
-- statement:
--   Every traced residue coefficient of the one-place product differential
--   away from the selected place is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueProduct.lean#L119-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueProduct.lean#L119-L140

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

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero_of_ne
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P Q : GlobalPlace k F) (hQP : Q ≠ P)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) Q = 0 := by sorry
