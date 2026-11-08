-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_pieceCrossingCoefficients_spec
-- name    : QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCoefficients_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:40:04.472502+00:00
-- url     : https://prove2.me/theorems/ff4c77d8-12d1-4cdb-90bc-fc5d130d372f
-- title:
--   BDL26 XLocal Weight Parity: piece Crossing Coefficients spec
-- statement:
--   Every even four-region word has the displayed explicit crossing chain,
--   with the exact source cost bound (the final edge has weight two).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L89-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean#L89-L101

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators

theorem QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCoefficients_spec (a b l r : ZMod 2)
    (hEven : a + b + l + r = 0) :
    let c := pieceCrossingCoefficients a b l r
    c 0 + c 1 = a ∧ c 2 + c 3 = b ∧
      c 0 + c 2 + c 4 = l ∧ c 1 + c 3 + c 4 = r ∧
      bitWeight (c 0) + bitWeight (c 1) + bitWeight (c 2) +
        bitWeight (c 3) + 2 * bitWeight (c 4) ≤ pieceCrossingCost a b l r := by sorry
