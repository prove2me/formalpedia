-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusYLaurentEvaluation_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusYLaurentEvaluation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:18:23.277307+00:00
-- url     : https://prove2.me/theorems/8972b6cd-04fe-40f4-a2a2-4aaac37f0c94
-- title:
--   Cartwright Steger: one Plus YLaurent Evaluation injective
-- statement:
--   The Cartwright Steger construction uses the one Plus YLaurent Evaluation injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L75-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L75-L85

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusYLaurentEvaluation_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (onePlusYLaurentEvaluation P r) := by sorry
