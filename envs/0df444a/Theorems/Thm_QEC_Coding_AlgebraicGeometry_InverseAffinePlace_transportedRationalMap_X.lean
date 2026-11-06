-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_transportedRationalMap_X
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:42.802965+00:00
-- url     : https://prove2.me/theorems/52001622-0791-4f67-b917-cff29e769922
-- title:
--   Inverse Affine Place: transported Rational Map X
-- statement:
--   The transported map sends the fresh chart variable to the reciprocal of
--   the original coordinate in `F`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L196-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L196-L201

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseAffinePlace
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
omit [Finite k]

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap_X :
    transportedRationalMap k F RatFunc.X = InverseChart.inverseCoordinate k F := by sorry
