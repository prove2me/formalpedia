-- Prove2me | Theorems.Thm_Supersequence_front
-- name    : Supersequence.front
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:56.492729+00:00
-- url     : https://prove2.me/theorems/719ea078-5403-5177-9eff-27b9183250fd
-- title:
--   Supersequence: front
-- statement:
--   The Supersequence construction uses the front property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L112-L116
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L112-L116

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
omit [DecidableEq α]

theorem Supersequence.front {x : α} {g r : List α} (hg : x ∉ g)
    (hw : Covers (fun _ => True) (g ++ r)) : Covers (· ≠ x) r := by sorry
