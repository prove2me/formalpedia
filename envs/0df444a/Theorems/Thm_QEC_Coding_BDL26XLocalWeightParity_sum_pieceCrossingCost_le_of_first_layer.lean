-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_sum_pieceCrossingCost_le_of_first_layer
-- name    : QEC.Coding.BDL26XLocalWeightParity.sum_pieceCrossingCost_le_of_first_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:39:52.793998+00:00
-- url     : https://prove2.me/theorems/5fb5585b-ebdd-4272-a733-68acc96a9e5c
-- title:
--   BDL26 XLocal Weight Parity: sum piece Crossing Cost le of first layer
-- statement:
--   Swapping the two layers gives the other branch of the source choice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L58-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L58-L76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators

theorem QEC.Coding.BDL26XLocalWeightParity.sum_pieceCrossingCost_le_of_first_layer
    {J : Type*} [Fintype J]
    (originalFirst originalSecond changedSecond left right : J → ZMod 2)
    (hLayer : (∑ j, bitWeight (originalFirst j)) ≤
      ∑ j, bitWeight (originalSecond j)) :
    (∑ j, pieceCrossingCost (originalFirst j) (changedSecond j) (left j) (right j)) ≤
      ∑ j, (bitWeight (originalFirst j) + bitWeight (originalSecond j) +
        bitWeight (left j) + bitWeight (right j)) := by sorry
