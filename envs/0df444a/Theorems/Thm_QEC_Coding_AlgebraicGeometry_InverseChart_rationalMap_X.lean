-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChart_rationalMap_X
-- name    : QEC.Coding.AlgebraicGeometry.InverseChart.rationalMap_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:36.888441+00:00
-- url     : https://prove2.me/theorems/ebf9242d-3421-47de-86ff-0a3ed42c13ac
-- title:
--   Inverse Chart: rational Map X
-- statement:
--   The new rational-function variable is sent to the reciprocal of the
--   original coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseChart.lean#L73-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseChart.lean#L73-L75

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseChart
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k k⟮X⟯ F]
variable [_root_.FunctionField k F]

theorem QEC.Coding.AlgebraicGeometry.InverseChart.rationalMap_X :
    rationalMap k F RatFunc.X = inverseCoordinate k F := by sorry
