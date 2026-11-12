-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraRegularNorm_eq_buildingDet_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_buildingDet_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:22:43.16772+00:00
-- url     : https://prove2.me/theorems/553f8b37-11d8-4fc6-87c1-fc3e637f3923
-- title:
--   Cartwright Steger: map cyclic Algebra Regular Norm eq building Det pow
-- statement:
--   The building determinant comparison holds for every element, including
--   nonunits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L277-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L277-L320

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_buildingDet_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r x) =
      Matrix.det (cyclicAlgebraToBuilding P r x) ^ r.matrixRank := by sorry
