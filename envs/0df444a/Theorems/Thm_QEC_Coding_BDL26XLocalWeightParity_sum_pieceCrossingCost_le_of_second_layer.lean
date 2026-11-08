-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_sum_pieceCrossingCost_le_of_second_layer
-- name    : QEC.Coding.BDL26XLocalWeightParity.sum_pieceCrossingCost_le_of_second_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:14:53.754568+00:00
-- url     : https://prove2.me/theorems/39e9f203-4e6d-4320-9f94-b0b993109393
-- title:
--   BDL26 XLocal Weight Parity: sum piece Crossing Cost le of second layer
-- statement:
--   The correction may change the first layer arbitrarily. If the untouched
--   second layer has smaller total parity weight, the total crossing budget is
--   bounded by the original four-region parity weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L43-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L43-L55

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators

theorem QEC.Coding.BDL26XLocalWeightParity.sum_pieceCrossingCost_le_of_second_layer
    {J : Type*} [Fintype J]
    (originalFirst originalSecond changedFirst left right : J → ZMod 2)
    (hLayer : (∑ j, bitWeight (originalSecond j)) ≤
      ∑ j, bitWeight (originalFirst j)) :
    (∑ j, pieceCrossingCost (changedFirst j) (originalSecond j) (left j) (right j)) ≤
      ∑ j, (bitWeight (originalFirst j) + bitWeight (originalSecond j) +
        bitWeight (left j) + bitWeight (right j)) := by sorry
