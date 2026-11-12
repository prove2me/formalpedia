-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraRegularNorm_eq_splittingDet_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_splittingDet_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:22:14.089991+00:00
-- url     : https://prove2.me/theorems/9df35e3c-a450-4579-a37a-2e1325d4aba2
-- title:
--   Cartwright Steger: map cyclic Algebra Regular Norm eq splitting Det pow
-- statement:
--   The global splitting determinant comparison also holds for every
--   element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L324-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L324-L363

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_splittingDet_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r x) =
      Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ^ r.matrixRank := by sorry
