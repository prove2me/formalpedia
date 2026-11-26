-- Prove2me | Theorems.Thm_Supersequence_transportNine
-- name    : Supersequence.transportNine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:15.301658+00:00
-- url     : https://prove2.me/theorems/3310c136-a347-4855-892a-28ccd2904a50
-- title:
--   Supersequence: transport Nine
-- statement:
--   The Supersequence construction uses the transport Nine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L256-L267
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L256-L267

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.transportNine (nine : ∀ v : List (Fin 9), Universal v → 66 ≤ v.length)
    (x : Fin 10) : LowerOnOthers x 66 := by sorry
