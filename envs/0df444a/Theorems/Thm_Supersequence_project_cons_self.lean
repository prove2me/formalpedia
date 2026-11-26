-- Prove2me | Theorems.Thm_Supersequence_project_cons_self
-- name    : Supersequence.project_cons_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:50.686247+00:00
-- url     : https://prove2.me/theorems/45909dcd-62fa-40bf-a6c7-4a9813d09d15
-- title:
--   Supersequence: project cons self
-- statement:
--   The Supersequence construction uses the project cons self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L91-L92
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L91-L92

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.project_cons_self (x : α) (w : List α) :
    project x (x :: w) = project x w := by sorry
