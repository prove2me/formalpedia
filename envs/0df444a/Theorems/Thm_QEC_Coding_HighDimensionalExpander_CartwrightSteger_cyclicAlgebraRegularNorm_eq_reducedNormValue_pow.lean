-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraRegularNorm_eq_reducedNormValue_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_eq_reducedNormValue_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:22:23.795621+00:00
-- url     : https://prove2.me/theorems/58aa3d57-6f39-4993-8771-bdf3e9e76040
-- title:
--   Cartwright Steger: cyclic Algebra Regular Norm eq reduced Norm Value pow
-- statement:
--   The intrinsic regular norm is the `d`-th power of the descended reduced
--   norm, already over the base function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L367-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L367-L373

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_eq_reducedNormValue_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraRegularNorm P r x =
      cyclicAlgebraReducedNormValue P r x ^ r.matrixRank := by sorry
