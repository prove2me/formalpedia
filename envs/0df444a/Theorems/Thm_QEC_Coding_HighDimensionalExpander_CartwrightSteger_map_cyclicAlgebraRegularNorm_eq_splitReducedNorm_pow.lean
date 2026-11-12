-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraRegularNorm_eq_splitReducedNorm_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_splitReducedNorm_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:25:39.927627+00:00
-- url     : https://prove2.me/theorems/15d637c2-f063-4994-89f8-385ab5b9eda6
-- title:
--   Cartwright Steger: map cyclic Algebra Regular Norm eq split Reduced Norm pow
-- statement:
--   The global splitting reduced norm has `d`-th power equal to the scalar
--   extension of the intrinsic regular norm, for every global unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L239-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L239-L257

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_splitReducedNorm_pow
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraSplitReducedNorm P r u :
          (SplittingFunctionField P r)ˣ) :
        SplittingFunctionField P r) ^ r.matrixRank := by sorry
