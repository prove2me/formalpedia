-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_uniformizerLogDifferentialClass
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv_uniformizerLogDifferentialClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:32:16.88209+00:00
-- url     : https://prove2.me/theorems/b0bed08b-a471-4ee0-abbd-550266dc3a3d
-- title:
--   Differential: simple Pole Residue Equiv uniformizer Log Differential Class
-- statement:
--   The normalized equivalence sends the logarithmic differential of the
--   normalized uniformizer to `1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L62-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L62-L71

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv_uniformizerLogDifferentialClass
    (P : GlobalPlace k F) :
    simplePoleResidueEquiv (k := k) (F := F) P
        (uniformizerLogDifferentialClass (k := k) (F := F) P) = 1 := by sorry
