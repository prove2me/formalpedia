-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraSplitNormOneGeneratorRatio_ne_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:13:58.207478+00:00
-- url     : https://prove2.me/theorems/18f20b42-dedd-43ae-8280-89d1168d4f65
-- title:
--   Cartwright Steger: cyclic Algebra Split Norm One Generator Ratio ne one
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Split Norm One Generator Ratio ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L32-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L32-L43

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_ne_one
    (P : BasePrime) (r : Rank)
    {u v : ConstantProjectiveClass P r} (huv : u ≠ v) :
    cyclicAlgebraSplitNormOneGeneratorRatio P r u v ≠ 1 := by sorry
