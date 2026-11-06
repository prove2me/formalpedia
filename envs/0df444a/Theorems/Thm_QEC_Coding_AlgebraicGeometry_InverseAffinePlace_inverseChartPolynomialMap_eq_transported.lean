-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_inverseChartPolynomialMap_eq_transported
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartPolynomialMap_eq_transported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:06.33583+00:00
-- url     : https://prove2.me/theorems/1c3d905e-af92-4557-ba4f-1bef8df2b1dc
-- title:
--   Inverse Affine Place: inverse Chart Polynomial Map eq transported
-- statement:
--   The polynomial maps agree after the rational-map compatibility is made
--   explicit, so the inverse-chart polynomial algebra is not a second assumed
--   chart structure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L247-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L247-L254

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartPolynomialMap_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.polynomialMap k F) = transportedPolynomialMap k F := by sorry
