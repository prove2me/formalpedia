-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:10.663052+00:00
-- url     : https://prove2.me/theorems/54913592-e0f7-4111-8b05-a9268cfc8f17
-- title:
--   Differential: global Simple Pole Residue Sum eq zero
-- statement:
--   The sum of the traced normalized residues of a global function-field
--   differential with at most simple poles is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/FunctionFieldGlobalResidue.lean#L609-L645
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/FunctionFieldGlobalResidue.lean#L609-L645

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_GlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.functionFieldGlobalResidue_Algebra_2
attribute [local instance] functionFieldGlobalResidue_Algebra_2
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.functionFieldGlobalResidue_ScalarTower_2
attribute [local instance] functionFieldGlobalResidue_ScalarTower_2

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_eq_zero
    (omega : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega) :
    globalSimplePoleResidueSum (k := k) (F := F) omega homega = 0 := by sorry
