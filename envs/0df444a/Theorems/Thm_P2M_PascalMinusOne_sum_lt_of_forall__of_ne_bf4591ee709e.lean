-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e
-- name    : P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:20.136255+00:00
-- url     : https://prove2.me/theorems/7b2db21e-23d0-5016-a7df-584e0fc0bd0e
-- title:
--   P2 M Pascal Minus One sum lt of forall  of ne bf4591ee709e: P2 M Pascal Minus One sum lt of forall  of ne bf4591ee709e
-- statement:
--   If two equal-length digit lists are componentwise ordered and not equal, their digit sums
--   are strictly ordered.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L171-L187
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L171-L187

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) (hne : S ≠ D) :
    S.sum < D.sum := by sorry

alias «PascalMinusOne».«sum_lt_of_forall₂_of_ne» := P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e
