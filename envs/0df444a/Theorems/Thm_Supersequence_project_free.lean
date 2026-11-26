-- Prove2me | Theorems.Thm_Supersequence_project_free
-- name    : Supersequence.project_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:52.726747+00:00
-- url     : https://prove2.me/theorems/25e4bc3e-ff90-4926-ac6a-2fbefa84b31f
-- title:
--   Supersequence: project free
-- statement:
--   The Supersequence construction uses the project free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L97-L101
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L97-L101

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.project_free {x : α} {w : List α} (h : x ∉ w) : project x w = w := by sorry
