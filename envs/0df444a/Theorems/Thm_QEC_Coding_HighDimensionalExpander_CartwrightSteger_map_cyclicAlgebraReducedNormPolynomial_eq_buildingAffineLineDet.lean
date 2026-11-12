-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormPolynomial_eq_buildingAffineLineDet
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormPolynomial_eq_buildingAffineLineDet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:23:12.39656+00:00
-- url     : https://prove2.me/theorems/c8da1b18-5dcc-4caf-b0f0-eef3aa36fe9d
-- title:
--   Cartwright Steger: map cyclic Algebra Reduced Norm Polynomial eq building Affine Line Det
-- statement:
--   The descended normalized reduced-norm polynomial agrees exactly with the
--   building-place determinant polynomial, not merely after taking a power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L559-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L559-L571

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormPolynomial_eq_buildingAffineLineDet
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (algebraMap (FunctionField P) (BuildingLocalField P))
        (cyclicAlgebraReducedNormPolynomial P r x) =
      Matrix.affineLineDet (cyclicAlgebraToBuilding P r x) := by sorry
