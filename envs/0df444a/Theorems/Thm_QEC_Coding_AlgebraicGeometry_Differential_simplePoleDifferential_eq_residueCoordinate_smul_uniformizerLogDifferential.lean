-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:42.473206+00:00
-- url     : https://prove2.me/theorems/ec927d79-3d1d-4d3a-9115-ad2922c0f557
-- title:
--   Differential: simple Pole Differential eq residue Coordinate smul uniformizer Log Differential
-- statement:
--   A simple-pole differential is reconstructed from its regular residue
--   coordinate and the normalized uniformizer logarithmic differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean#L118-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean#L118-L145

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
    (P : GlobalPlace k F) (omega : simplePoleDifferentialLattice P) :
    (omega : Differential k F) =
      simplePoleResidueCoordinate (k := k) (F := F) P omega •
        (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) := by sorry
