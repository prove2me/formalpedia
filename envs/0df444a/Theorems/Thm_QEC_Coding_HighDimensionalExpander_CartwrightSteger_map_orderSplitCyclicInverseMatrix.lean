-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCyclicInverseMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCyclicInverseMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:28.565638+00:00
-- url     : https://prove2.me/theorems/83a9eb77-3d3a-4b3e-9a0b-1a9f59ad5f0e
-- title:
--   Cartwright Steger: map order Split Cyclic Inverse Matrix
-- statement:
--   The Cartwright Steger construction uses the map order Split Cyclic Inverse Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L348-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L348-L356

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCyclicInverseMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderSplitCyclicInverseMatrix P r).map
        (indexConstantArithmeticEval P r level) =
      indexCyclicGeneratorInverseMatrix P r level := by sorry
