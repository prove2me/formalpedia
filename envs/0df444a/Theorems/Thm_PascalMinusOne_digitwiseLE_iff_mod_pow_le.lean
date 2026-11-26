-- Prove2me | Theorems.Thm_PascalMinusOne_digitwiseLE_iff_mod_pow_le
-- name    : PascalMinusOne.digitwiseLE_iff_mod_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:48.54922+00:00
-- url     : https://prove2.me/theorems/1398f107-7c9a-5d28-ae72-41fea2b452e9
-- title:
--   Pascal Minus One: digitwise LE iff mod pow le
-- statement:
--   Digitwise comparison is equivalent to comparison of every base-`p` prefix.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L36-L69
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean#L36-L69

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.digitwiseLE_iff_mod_pow_le {p k n : ℕ} (hp : 0 < p) :
    DigitwiseLE p k n ↔ ∀ i, k % p ^ i ≤ n % p ^ i := by sorry
