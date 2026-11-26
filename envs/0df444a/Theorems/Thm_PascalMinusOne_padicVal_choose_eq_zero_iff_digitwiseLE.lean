-- Prove2me | Theorems.Thm_PascalMinusOne_padicVal_choose_eq_zero_iff_digitwiseLE
-- name    : PascalMinusOne.padicVal_choose_eq_zero_iff_digitwiseLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:05.264508+00:00
-- url     : https://prove2.me/theorems/4286f59c-9c70-544c-b4fc-a67102d44995
-- title:
--   Pascal Minus One: padic Val choose eq zero iff digitwise LE
-- statement:
--   Zero valuation iff every base-`p` digit of `k` lies below that of `n`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L124-L169
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L124-L169

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.padicVal_choose_eq_zero_iff_digitwiseLE {p n k : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) :
    padicValNat p (n.choose k) = 0 ↔ DigitwiseLE p k n := by sorry
