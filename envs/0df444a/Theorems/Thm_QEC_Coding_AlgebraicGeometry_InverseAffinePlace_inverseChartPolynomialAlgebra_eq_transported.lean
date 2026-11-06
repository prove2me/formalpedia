-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_inverseChartPolynomialAlgebra_eq_transported
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartPolynomialAlgebra_eq_transported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:58.920061+00:00
-- url     : https://prove2.me/theorems/1dba915e-4215-46a7-9b4a-5060315bf712
-- title:
--   Inverse Affine Place: inverse Chart Polynomial Algebra eq transported
-- statement:
--   Equality of the concrete polynomial maps gives equality of their induced
--   algebra structures.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L258-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L258-L265

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartPolynomialAlgebra_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.polynomialMap k F).toAlgebra = transportedPolynomialAlgebra k F := by sorry
