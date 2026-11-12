-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNormPolynomial_eval
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:23:46.468675+00:00
-- url     : https://prove2.me/theorems/944643c0-5cf2-4590-b6e7-4c80eb61436b
-- title:
--   Cartwright Steger: cyclic Algebra Reduced Norm Polynomial eval
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Reduced Norm Polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L471-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L471-L498

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_eval
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) (a : FunctionField P) :
    Polynomial.eval a (cyclicAlgebraReducedNormPolynomial P r x) =
      cyclicAlgebraReducedNormValue P r (1 + a • (x - 1)) := by sorry
