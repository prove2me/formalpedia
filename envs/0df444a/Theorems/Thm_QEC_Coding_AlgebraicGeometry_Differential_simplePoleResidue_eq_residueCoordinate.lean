-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_residueCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_residueCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:34.772827+00:00
-- url     : https://prove2.me/theorems/60174013-e9ce-4e3d-9003-6c08a1e6d299
-- title:
--   Differential: simple Pole Residue eq residue Coordinate
-- statement:
--   The normalized simple-pole residue is reduction of the explicit regular
--   residue coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean#L149-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean#L149-L172

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_residueCoordinate (P : GlobalPlace k F)
    (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P omega =
      P.residue (simplePoleResidueCoordinate (k := k) (F := F) P omega) := by sorry
