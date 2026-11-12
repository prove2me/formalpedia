-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNormPolynomial_eval_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_eval_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:23:14.548308+00:00
-- url     : https://prove2.me/theorems/f947d866-1cb7-4372-82a9-d00bf2ca0c5c
-- title:
--   Cartwright Steger: cyclic Algebra Reduced Norm Polynomial eval one
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Reduced Norm Polynomial eval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L448-L469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L448-L469

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_eval_one
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.eval 1 (cyclicAlgebraReducedNormPolynomial P r x) =
      cyclicAlgebraReducedNormValue P r x := by sorry
