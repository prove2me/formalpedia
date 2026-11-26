-- Prove2me | Theorems.Thm_Supersequence_project_append
-- name    : Supersequence.project_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:50.054609+00:00
-- url     : https://prove2.me/theorems/c814da6e-3183-4233-a356-da65976a4b4f
-- title:
--   Supersequence: project append
-- statement:
--   The Supersequence construction uses the project append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L88-L89
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L88-L89

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.project_append (x : α) (a b : List α) :
    project x (a ++ b) = project x a ++ project x b := by sorry
