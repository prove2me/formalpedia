-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_ne_one_cyclicAlgebraSplitNormOne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_ne_one_cyclicAlgebraSplitNormOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:26:02.453688+00:00
-- url     : https://prove2.me/theorems/1a6a9dac-02ab-4e17-9bed-5187797a36d6
-- title:
--   Cartwright Steger: exists ne one cyclic Algebra Split Norm One
-- statement:
--   The Cartwright Steger construction uses the exists ne one cyclic Algebra Split Norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L45-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L45-L54

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_ne_one_cyclicAlgebraSplitNormOne
    (P : BasePrime) (r : Rank) :
    ∃ g : CyclicAlgebraSplitNormOne P r, g ≠ 1 := by sorry
