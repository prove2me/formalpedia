-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:21:56.25056+00:00
-- url     : https://prove2.me/theorems/fe6cf2d8-461a-410f-ae32-96bdb3e8adf8
-- title:
--   Cartwright Steger: cyclic Algebra Reduced Norm base Change eq split Reduced Norm
-- statement:
--   The old determinant-valued split norm is exactly the scalar extension of
--   the descended base-function-field reduced norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L261-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L261-L271

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Units.map (functionFieldEmbedding P r)
        (cyclicAlgebraReducedNorm P r u) =
      cyclicAlgebraSplitReducedNorm P r u := by sorry
