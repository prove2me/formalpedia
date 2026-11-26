-- Prove2me | Theorems.Thm_Supersequence_remainingFrequencies
-- name    : Supersequence.remainingFrequencies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:09:53.129522+00:00
-- url     : https://prove2.me/theorems/44c00b69-f016-446a-b6d7-4a64f13812ba
-- title:
--   Supersequence: remaining Frequencies
-- statement:
--   The remaining computational branches exhaust the possible minimum frequencies.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L367-L376
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L367-L376

import Definitions.Def_Frequency
import Definitions.Def_Four
set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]

theorem Supersequence.remainingFrequencies {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) (f9 : LengthBound 9 66)
    (x : Fin 10) (least : ∀ a, w.count x ≤ w.count a) :
    w.count x = 5 ∨ w.count x = 6 ∨ w.count x = 7 := by sorry
