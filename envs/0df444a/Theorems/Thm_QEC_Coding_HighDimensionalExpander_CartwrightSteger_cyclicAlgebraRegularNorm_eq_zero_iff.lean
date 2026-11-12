-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraRegularNorm_eq_zero_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:25:20.472901+00:00
-- url     : https://prove2.me/theorems/5d6bb7a0-6f20-4d0c-85b2-d6058ac07b8b
-- title:
--   Cartwright Steger: cyclic Algebra Regular Norm eq zero iff
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Regular Norm eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L36-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L36-L40

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_eq_zero_iff
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraRegularNorm P r x = 0 ↔ x = 0 := by sorry
