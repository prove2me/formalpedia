-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldOnePlusYLaurentEvaluation_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldOnePlusYLaurentEvaluation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:18:03.447684+00:00
-- url     : https://prove2.me/theorems/1e073490-11a1-4eef-b6d3-1bb5d921d055
-- title:
--   Cartwright Steger: function Field One Plus YLaurent Evaluation injective
-- statement:
--   The Cartwright Steger construction uses the function Field One Plus YLaurent Evaluation injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L146-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L146-L156

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldOnePlusYLaurentEvaluation_injective
    (P : BasePrime) :
    Function.Injective (functionFieldOnePlusYLaurentEvaluation P) := by sorry
