-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:21:45.577579+00:00
-- url     : https://prove2.me/theorems/454a6a8d-fb1f-4c0a-b92e-3811368f12a1
-- title:
--   Cartwright Steger: splitting Cyclic Scalar Extension regular Norm eq split Reduced Norm pow
-- statement:
--   In the global splitting, the regular norm of a scalar-extended global
--   unit is the `d`-th power of the fixed splitting reduced norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L194-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L194-L235

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Algebra.norm (SplittingFunctionField P r)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := SplittingFunctionField P r)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraSplitReducedNorm P r u :
          (SplittingFunctionField P r)ˣ) :
        SplittingFunctionField P r) ^ r.matrixRank := by sorry
