-- Prove2me | Theorems.Thm_Supersequence_fourGaps
-- name    : Supersequence.fourGaps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:18.477643+00:00
-- url     : https://prove2.me/theorems/3a727ee9-6770-57f6-974d-27410392b69b
-- title:
--   Supersequence: four Gaps
-- statement:
--   Display the five pivot-free gaps of a four-copy word.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L304-L315
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L304-L315

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.fourGaps {x : α} {w : List α} (hw : w.count x = 4) :
    ∃ a b c d e : List α, w = a ++ x :: (b ++ x :: (c ++ x :: (d ++ x :: e))) ∧
      x ∉ a ∧ x ∉ b ∧ x ∉ c ∧ x ∉ d ∧ x ∉ e := by sorry
