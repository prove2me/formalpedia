-- Prove2me | Theorems.Thm_Supersequence_projected_bound
-- name    : Supersequence.projected_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:55.379623+00:00
-- url     : https://prove2.me/theorems/3210a26a-c467-5a6b-bad2-3d5d1d1dec7b
-- title:
--   Supersequence: projected bound
-- statement:
--   The Supersequence construction uses the projected bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L103-L109
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L103-L109

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.projected_bound {x : α} {w : List α} {F : Nat}
    (low : LowerOnOthers x F) (cov : Covers (· ≠ x) w) : F ≤ (project x w).length := by sorry
