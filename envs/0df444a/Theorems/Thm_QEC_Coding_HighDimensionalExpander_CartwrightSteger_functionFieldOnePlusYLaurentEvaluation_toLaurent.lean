-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldOnePlusYLaurentEvaluation_toLaurent
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldOnePlusYLaurentEvaluation_toLaurent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:17:24.411778+00:00
-- url     : https://prove2.me/theorems/10fd5742-d2d7-4672-a564-e5971c874dbc
-- title:
--   Cartwright Steger: function Field One Plus YLaurent Evaluation to Laurent
-- statement:
--   The Cartwright Steger construction uses the function Field One Plus YLaurent Evaluation to Laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L98-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L98-L116

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldOnePlusYLaurentEvaluation_toLaurent
    (P : BasePrime) (f : PolynomialRing P) :
    functionFieldOnePlusYLaurentEvaluation P (Polynomial.toLaurent f) =
      algebraMap (PolynomialRing P) (FunctionField P)
        (f.comp (Polynomial.X + 1)) := by sorry
