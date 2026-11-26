-- Prove2me | Theorems.Thm_PascalMinusOne_G_ne_zero
-- name    : PascalMinusOne.G_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:00.242501+00:00
-- url     : https://prove2.me/theorems/6c41dfb2-612e-46c4-ae00-76a10bbd39e6
-- title:
--   Pascal Minus One: G ne zero
-- statement:
--   The restricted gcd is nonzero as soon as the admissible set contains the index `m`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L37-L41
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L37-L41

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.G_ne_zero {N m : ℕ} (hm : 0 < m) (hNm : m < N) :
    G N m ≠ 0 := by sorry
