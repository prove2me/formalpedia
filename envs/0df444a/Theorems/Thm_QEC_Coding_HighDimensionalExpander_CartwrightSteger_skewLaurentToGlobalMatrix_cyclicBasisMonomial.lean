-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_cyclicBasisMonomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_cyclicBasisMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:58:15.408494+00:00
-- url     : https://prove2.me/theorems/a29d3034-aebb-4d9c-b087-e432240b2f4c
-- title:
--   Cartwright Steger: skew Laurent To Global Matrix cyclic Basis Monomial
-- statement:
--   The Cartwright Steger construction uses the skew Laurent To Global Matrix cyclic Basis Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L288-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L288-L303

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_cyclicBasisMonomial
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentToGlobalMatrix P r
        (skewLaurentCyclicBasisMonomial P r p) =
      (functionFieldCyclicBasisVector P r p :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by sorry
