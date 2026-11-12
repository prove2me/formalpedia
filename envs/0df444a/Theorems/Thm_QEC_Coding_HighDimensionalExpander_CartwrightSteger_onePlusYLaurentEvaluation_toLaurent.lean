-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusYLaurentEvaluation_toLaurent
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusYLaurentEvaluation_toLaurent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:16:48.781506+00:00
-- url     : https://prove2.me/theorems/83ac1207-1b9c-4abd-b172-00de3d0fc114
-- title:
--   Cartwright Steger: one Plus YLaurent Evaluation to Laurent
-- statement:
--   The Cartwright Steger construction uses the one Plus YLaurent Evaluation to Laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L26-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L26-L46

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusYLaurentEvaluation_toLaurent
    (P : BasePrime) (r : Rank)
    (f : Polynomial (ConstantExtension P r)) :
    onePlusYLaurentEvaluation P r (Polynomial.toLaurent f) =
      algebraMap (Polynomial (ConstantExtension P r))
        (SplittingFunctionField P r)
          (f.comp (Polynomial.X + 1)) := by sorry
