-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_pieceCrossingCost_le_twice_second
-- name    : QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCost_le_twice_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:14:07.069189+00:00
-- url     : https://prove2.me/theorems/c90c9b0d-8797-4f4a-af9f-7422b3069f87
-- title:
--   BDL26 XLocal Weight Parity: piece Crossing Cost le twice second
-- statement:
--   The BDL26 XLocal Weight Parity construction uses the piece Crossing Cost le twice second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L29-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L29-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators

theorem QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCost_le_twice_second (a b l r : ZMod 2) :
    pieceCrossingCost a b l r ≤
      bitWeight b + bitWeight b + bitWeight l + bitWeight r := by sorry
