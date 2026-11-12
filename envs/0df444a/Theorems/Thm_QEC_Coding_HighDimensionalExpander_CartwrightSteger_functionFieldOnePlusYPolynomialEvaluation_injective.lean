-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldOnePlusYPolynomialEvaluation_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldOnePlusYPolynomialEvaluation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:18:00.852449+00:00
-- url     : https://prove2.me/theorems/dc9c3472-6a39-4f69-9ff4-d567715acddb
-- title:
--   Cartwright Steger: function Field One Plus YPolynomial Evaluation injective
-- statement:
--   The Cartwright Steger construction uses the function Field One Plus YPolynomial Evaluation injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L118-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L118-L144

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldOnePlusYPolynomialEvaluation_injective
    (P : BasePrime) :
    Function.Injective
      (fun f : PolynomialRing P =>
        Polynomial.eval₂
          (algebraMap (BaseField P) (FunctionField P))
          (1 + RatFunc.X) f) := by sorry
