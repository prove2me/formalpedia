-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_inverseChartRationalAlgebra_eq_transported
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartRationalAlgebra_eq_transported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:39.195023+00:00
-- url     : https://prove2.me/theorems/a00d48ac-3644-499e-8d06-daa3fdeca3cd
-- title:
--   Inverse Affine Place: inverse Chart Rational Algebra eq transported
-- statement:
--   The inverse-chart algebra specified in `InverseChart` is therefore the
--   same algebra as the one for which finite-dimensionality and separability were
--   transported above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L235-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L235-L242

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartRationalAlgebra_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.rationalMap k F).toRingHom.toAlgebra = transportedRationalAlgebra k F := by sorry
