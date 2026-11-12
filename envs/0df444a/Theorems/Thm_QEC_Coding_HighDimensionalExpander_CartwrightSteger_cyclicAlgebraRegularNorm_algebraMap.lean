-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraRegularNorm_algebraMap
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:24:55.247922+00:00
-- url     : https://prove2.me/theorems/a1e75729-e41e-458f-8de4-3fe3ce005b9c
-- title:
--   Cartwright Steger: cyclic Algebra Regular Norm algebra Map
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Regular Norm algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L27-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L27-L34

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_algebraMap
    (P : BasePrime) (r : Rank) (a : FunctionField P) :
    cyclicAlgebraRegularNorm P r
        (algebraMap (FunctionField P) (CyclicAlgebra P r) a) =
      a ^ (r.matrixRank * r.matrixRank) := by sorry
