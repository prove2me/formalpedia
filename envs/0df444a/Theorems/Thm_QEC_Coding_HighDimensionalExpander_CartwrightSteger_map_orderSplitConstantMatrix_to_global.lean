-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitConstantMatrix_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitConstantMatrix_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:49:17.485986+00:00
-- url     : https://prove2.me/theorems/6677f447-f8aa-4b98-99e7-5c4b9d13b043
-- title:
--   Cartwright Steger: map order Split Constant Matrix to global
-- statement:
--   The Cartwright Steger construction uses the map order Split Constant Matrix to global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L358-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L358-L365

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitConstantMatrix_to_global
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (orderSplitConstantMatrix P r c).map
        (constantArithmeticToSplittingFunctionField P r) =
      constantMatrix P r c := by sorry
