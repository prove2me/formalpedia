-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_simplePoleResidueCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_simplePoleResidueCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:38.124715+00:00
-- url     : https://prove2.me/theorems/27483b98-df33-46a8-8306-c029b2c3403f
-- title:
--   Differential: coe simple Pole Residue Coordinate
-- statement:
--   The ambient field value represented by the residue coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean#L92-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean#L92-L101

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_simplePoleResidueCoordinate (P : GlobalPlace k F)
    (omega : simplePoleDifferentialLattice P) :
    ((simplePoleResidueCoordinate (k := k) (F := F) P omega :
      P.valuationRing) : F) =
      (P.uniformizerInValuationRing : F) *
        functionFieldDifferentialCoordinate (k := k) (F := F)
          (omega : Differential k F) *
        (functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F))⁻¹ := by sorry
