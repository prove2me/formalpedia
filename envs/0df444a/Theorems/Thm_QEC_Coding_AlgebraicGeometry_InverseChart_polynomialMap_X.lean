-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChart_polynomialMap_X
-- name    : QEC.Coding.AlgebraicGeometry.InverseChart.polynomialMap_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:45.11952+00:00
-- url     : https://prove2.me/theorems/8b6a61c8-066d-4f28-a065-1140493d8b75
-- title:
--   Inverse Chart: polynomial Map X
-- statement:
--   The inverse-chart polynomial variable evaluates to the reciprocal of the
--   original rational coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseChart.lean#L98-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseChart.lean#L98-L100

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

theorem QEC.Coding.AlgebraicGeometry.InverseChart.polynomialMap_X :
    polynomialMap k F Polynomial.X = inverseCoordinate k F := by sorry
