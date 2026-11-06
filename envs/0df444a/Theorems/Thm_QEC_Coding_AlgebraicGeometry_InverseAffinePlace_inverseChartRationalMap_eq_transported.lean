-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_inverseChartRationalMap_eq_transported
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartRationalMap_eq_transported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:21.009895+00:00
-- url     : https://prove2.me/theorems/c4b71f5e-b01b-436d-9a78-5505b3121203
-- title:
--   Inverse Affine Place: inverse Chart Rational Map eq transported
-- statement:
--   The transported inverse chart supplies the same `X ↦ t⁻¹` rational map as
--   `InverseChart.rationalMap`.  This is proved by fraction-field extensionality:
--   both maps agree on constants and on the polynomial variable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L206-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L206-L230

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartRationalMap_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.rationalMap k F).toRingHom = transportedRationalMap k F := by sorry
