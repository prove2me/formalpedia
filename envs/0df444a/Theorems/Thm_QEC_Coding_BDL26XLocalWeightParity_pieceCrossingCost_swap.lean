-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_pieceCrossingCost_swap
-- name    : QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCost_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:14:16.287665+00:00
-- url     : https://prove2.me/theorems/608a3700-7804-4ddb-a068-71480b8e9fa8
-- title:
--   BDL26 XLocal Weight Parity: piece Crossing Cost swap
-- statement:
--   The BDL26 XLocal Weight Parity construction uses the piece Crossing Cost swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L36-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L36-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators

theorem QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCost_swap (a b l r : ZMod 2) :
    pieceCrossingCost a b l r = pieceCrossingCost b a l r := by sorry
