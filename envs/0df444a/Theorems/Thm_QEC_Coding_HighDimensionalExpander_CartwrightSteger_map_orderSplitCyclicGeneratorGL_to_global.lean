-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCyclicGeneratorGL_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCyclicGeneratorGL_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:40.943204+00:00
-- url     : https://prove2.me/theorems/e49a6eef-93ee-42b2-9c07-26e2dab9da21
-- title:
--   Cartwright Steger: map order Split Cyclic Generator GL to global
-- statement:
--   The Cartwright Steger construction uses the map order Split Cyclic Generator GL to global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L664-L670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L664-L670

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCyclicGeneratorGL_to_global
    (P : BasePrime) (r : Rank) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCyclicGeneratorGL P r) =
      cyclicGenerator P r := by sorry
