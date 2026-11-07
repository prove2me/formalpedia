-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitBGL_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitBGL_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:49:30.809628+00:00
-- url     : https://prove2.me/theorems/51e4c36b-9242-4e54-9fde-a40766819d01
-- title:
--   Cartwright Steger: map order Split BGL to global
-- statement:
--   The Cartwright Steger construction uses the map order Split BGL to global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L681-L703
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L681-L703

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitBGL_to_global
    (P : BasePrime) (r : Rank) :
    orderSplitBaseChangeGLHom P r (orderSplitBGL P r) =
      cartwrightStegerB P r := by sorry
