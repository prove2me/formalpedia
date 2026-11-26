-- Prove2me | Theorems.Thm_Supersequence_length_account
-- name    : Supersequence.length_account
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:09.163128+00:00
-- url     : https://prove2.me/theorems/f7f1cffb-ac70-5de6-86a7-c8e2186c37f5
-- title:
--   Supersequence: length account
-- statement:
--   The Supersequence construction uses the length account property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L125-L132
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L125-L132

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.length_account (x : α) (w : List α) :
    (project x w).length + w.count x = w.length := by sorry
