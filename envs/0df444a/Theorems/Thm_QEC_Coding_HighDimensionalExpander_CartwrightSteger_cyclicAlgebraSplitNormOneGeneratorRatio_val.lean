-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraSplitNormOneGeneratorRatio_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:13:46.38622+00:00
-- url     : https://prove2.me/theorems/9cb973e7-dd61-4b43-b101-7a560dd38cc1
-- title:
--   Cartwright Steger: cyclic Algebra Split Norm One Generator Ratio val
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Split Norm One Generator Ratio val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L23-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L23-L30

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    (cyclicAlgebraSplitNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) =
      (cyclicAlgebraBuildingNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
