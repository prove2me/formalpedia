-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_matrixRank_isUnit_buildingLocalField
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.matrixRank_isUnit_buildingLocalField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:23:05.898408+00:00
-- url     : https://prove2.me/theorems/e379c595-57c2-4aa8-ab5c-120fd9ffd837
-- title:
--   Cartwright Steger: matrix Rank is Unit building Local Field
-- statement:
--   The matrix rank is invertible at the building place.  This is precisely
--   where the source restriction `q ≥ 5` excludes characteristics dividing
--   `d = 3` or `d = 4`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L532-L555
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L532-L555

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.matrixRank_isUnit_buildingLocalField
    (P : BasePrime) (r : Rank) :
    IsUnit (r.matrixRank : BuildingLocalField P) := by sorry
