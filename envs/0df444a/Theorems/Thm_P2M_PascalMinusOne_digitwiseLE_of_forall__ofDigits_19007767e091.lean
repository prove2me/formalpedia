-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091
-- name    : P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:32.909874+00:00
-- url     : https://prove2.me/theorems/6bb73347-e8b7-43f2-807c-c7cf655e3a2d
-- title:
--   P2 M Pascal Minus One digitwise LE of forall  of Digits 19007767e091: P2 M Pascal Minus One digitwise LE of forall  of Digits 19007767e091
-- statement:
--   A componentwise comparison of valid base-`p` digit lists gives `DigitwiseLE`
--   for the represented natural numbers.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L239-L246
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L239-L246

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091 {p : ℕ} (hp : 2 ≤ p) {S D : List ℕ}
    (hSD : List.Forall₂ (· ≤ ·) S D)
    (hS : ∀ s ∈ S, s < p)
    (hD : ∀ d ∈ D, d < p) :
    DigitwiseLE p (Nat.ofDigits p S) (Nat.ofDigits p D) := by sorry

alias «PascalMinusOne».«digitwiseLE_of_forall₂_ofDigits» := P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091
