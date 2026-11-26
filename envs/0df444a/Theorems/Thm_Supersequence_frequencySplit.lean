-- Prove2me | Theorems.Thm_Supersequence_frequencySplit
-- name    : Supersequence.frequencySplit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:16.71905+00:00
-- url     : https://prove2.me/theorems/04b39085-6a7b-4376-858f-13dd56a2c51e
-- title:
--   Supersequence: frequency Split
-- statement:
--   The only numerical input is the lower bound on words over Fin 9.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L270-L301
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L270-L301

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.frequencySplit (nine : ∀ v : List (Fin 9), Universal v → 66 ≤ v.length)
    {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82) :
    (∀ x, 4 ≤ w.count x) ∧ (∃ x, w.count x ≤ 7) := by sorry
