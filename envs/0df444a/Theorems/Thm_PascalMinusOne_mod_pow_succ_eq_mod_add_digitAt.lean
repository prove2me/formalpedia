-- Prove2me | Theorems.Thm_PascalMinusOne_mod_pow_succ_eq_mod_add_digitAt
-- name    : PascalMinusOne.mod_pow_succ_eq_mod_add_digitAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:36.122983+00:00
-- url     : https://prove2.me/theorems/caf947f6-a8e4-551d-87bf-64163d43b7e5
-- title:
--   Pascal Minus One: mod pow succ eq mod add digit At
-- statement:
--   The remainder modulo the next power is the old remainder plus the next base-`p` digit.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L30-L33
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L30-L33

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.mod_pow_succ_eq_mod_add_digitAt (p x i : ℕ) :
    x % p ^ (i + 1) = x % p ^ i + p ^ i * digitAt p x i := by sorry
