-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_integralArithmetic
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_integralArithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:57:47.819907+00:00
-- url     : https://prove2.me/theorems/8f6c130d-43c7-4f2f-9aab-e494e978ad25
-- title:
--   Cartwright Steger: exists skew Laurent of integral Arithmetic
-- statement:
--   The Cartwright Steger construction uses the exists skew Laurent of integral Arithmetic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L270-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L270-L279

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_integralArithmetic
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f =
        functionFieldScalarMatrix P r
          (integralArithmeticToFunctionField P a) := by sorry
