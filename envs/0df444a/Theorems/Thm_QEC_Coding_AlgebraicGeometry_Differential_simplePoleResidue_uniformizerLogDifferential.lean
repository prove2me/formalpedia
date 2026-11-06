-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_uniformizerLogDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_uniformizerLogDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:32:38.57526+00:00
-- url     : https://prove2.me/theorems/1e32f2ce-ff6d-4143-b99d-3c7f0585925a
-- title:
--   Differential: simple Pole Residue uniformizer Log Differential
-- statement:
--   The simple-pole residue of the normalized uniformizer's logarithmic
--   differential is `1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L110-L114

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_uniformizerLogDifferential (P : GlobalPlace k F) :
    simplePoleResidue (k := k) (F := F) P
        (uniformizerLogDifferential (k := k) (F := F) P) = 1 := by sorry
