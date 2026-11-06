-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_unitMulUniformizerLogDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_unitMulUniformizerLogDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:32:40.530723+00:00
-- url     : https://prove2.me/theorems/6f2cbb42-292c-4740-a054-750e3a058e6a
-- title:
--   Differential: simple Pole Residue unit Mul Uniformizer Log Differential
-- statement:
--   Multiplying the normalized uniformizer by a valuation-ring unit leaves
--   the normalized simple-pole residue equal to `1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L130-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L130-L139

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_unitMulUniformizerLogDifferential
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    simplePoleResidue (k := k) (F := F) P
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u) = 1 := by sorry
