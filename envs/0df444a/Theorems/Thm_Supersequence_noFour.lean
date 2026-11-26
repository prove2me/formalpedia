-- Prove2me | Theorems.Thm_Supersequence_noFour
-- name    : Supersequence.noFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:09:48.241348+00:00
-- url     : https://prove2.me/theorems/5439e885-aae1-4d18-ad3f-410e03d04f0a
-- title:
--   Supersequence: no Four
-- statement:
--   Four occurrences are impossible at length 82. The hypotheses are the
--   classical small-alphabet lower bounds and the separate nine-letter result.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L325-L364
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L325-L364

import Definitions.Def_Frequency
import Definitions.Def_Four
set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]

theorem Supersequence.noFour {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) (f9 : LengthBound 9 66) :
    ∀ x, w.count x ≠ 4 := by sorry
