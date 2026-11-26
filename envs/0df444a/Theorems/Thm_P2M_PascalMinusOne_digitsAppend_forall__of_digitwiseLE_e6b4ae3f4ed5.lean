-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5
-- name    : P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:43.884418+00:00
-- url     : https://prove2.me/theorems/cd16d547-4c67-429e-bbfc-da038d96bde9
-- title:
--   P2 M Pascal Minus One digits Append forall  of digitwise LE e6b4ae3f4ed5: P2 M Pascal Minus One digits Append forall  of digitwise LE e6b4ae3f4ed5
-- statement:
--   Digitwise containment is equivalent to componentwise containment after padding the smaller
--   digit list to the length of the ambient number.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L250-L282
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L250-L282

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5 {p k N : ℕ}
    (hp : 2 ≤ p) (hkn : k ≤ N) (hdigit : DigitwiseLE p k N) :
    List.Forall₂ (· ≤ ·)
      (Nat.digitsAppend p (Nat.digits p N).length k)
      (Nat.digits p N) := by sorry

alias «PascalMinusOne».«digitsAppend_forall₂_of_digitwiseLE» := P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5
