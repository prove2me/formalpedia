-- Prove2me | Theorems.Thm_PascalMinusOne_padicVal_choose_eq_carryCount
-- name    : PascalMinusOne.padicVal_choose_eq_carryCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:33.463247+00:00
-- url     : https://prove2.me/theorems/ffe00328-1a63-5cf4-8a7d-8c3acb89fad2
-- title:
--   Pascal Minus One: padic Val choose eq carry Count
-- statement:
--   Thin wrapper around Mathlib's Kummer theorem `padicValNat_choose`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L20-L23
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L20-L23

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.padicVal_choose_eq_carryCount {p n k b : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = carryCount p n k b := by sorry
