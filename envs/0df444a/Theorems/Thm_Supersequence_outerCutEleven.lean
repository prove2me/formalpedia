-- Prove2me | Theorems.Thm_Supersequence_outerCutEleven
-- name    : Supersequence.outerCutEleven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:09:51.652073+00:00
-- url     : https://prove2.me/theorems/c2674b51-fc52-4183-839f-6167f2ddfccb
-- title:
--   Supersequence: outer Cut Eleven
-- statement:
--   With one fewer position on the short side, every six of seven
--   singletons must be covered on the opposite side.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L268-L296
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L268-L296

import Definitions.Def_Frequency
import Definitions.Def_Four
set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]

theorem Supersequence.outerCutEleven {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 11) (cutOK : Compatible A p q)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) : 51 ≤ q.length := by sorry
