-- Prove2me | Theorems.Thm_Supersequence_back
-- name    : Supersequence.back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:00.842233+00:00
-- url     : https://prove2.me/theorems/bf116245-9bb4-587a-88ef-2b2dd2edca24
-- title:
--   Supersequence: back
-- statement:
--   The Supersequence construction uses the back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L119-L123
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L119-L123

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
omit [DecidableEq α]

theorem Supersequence.back {x : α} {l g : List α} (hg : x ∉ g)
    (hw : Covers (fun _ => True) (l ++ g)) : Covers (· ≠ x) l := by sorry
