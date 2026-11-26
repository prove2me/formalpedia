-- Prove2me | Theorems.Thm_Supersequence_skipGap
-- name    : Supersequence.skipGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:52.473587+00:00
-- url     : https://prove2.me/theorems/95c22308-34a0-47b2-96d8-53a2ceff8747
-- title:
--   Supersequence: skip Gap
-- statement:
--   The Supersequence construction uses the skip Gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L20-L29
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L20-L29

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}

theorem Supersequence.skipGap {x : α} {v g r : List α} (hx : x ∉ g)
    (h : (x :: v).Sublist (g ++ r)) : (x :: v).Sublist r := by sorry
