-- Prove2me | Theorems.Thm_PascalMinusOne_not_carryAt_iff_mod_pow_le
-- name    : PascalMinusOne.not_carryAt_iff_mod_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:34.951611+00:00
-- url     : https://prove2.me/theorems/3f3f7b7f-9f16-4535-9902-d24aca1d9285
-- title:
--   Pascal Minus One: not carry At iff mod pow le
-- statement:
--   Absence of a carry across `p^i` is exactly prefix comparison modulo `p^i`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L72-L121
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L72-L121

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.not_carryAt_iff_mod_pow_le {p n k i : ℕ} (hp : 0 < p) (hkn : k ≤ n) :
    ¬ CarryAt p n k i ↔ k % p ^ i ≤ n % p ^ i := by sorry
