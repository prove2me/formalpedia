-- Prove2me | Theorems.Thm_Supersequence_heavyLetter
-- name    : Supersequence.heavyLetter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:09:46.834725+00:00
-- url     : https://prove2.me/theorems/0455881e-7e91-4c57-98bb-c4ea19c8cc34
-- title:
--   Supersequence: heavy Letter
-- statement:
--   Every nonempty universal alphabet has a letter occurring at least its size times.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L112-L143
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L112-L143

import Definitions.Def_Frequency
import Definitions.Def_Four
set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]

theorem Supersequence.heavyLetter {A w : List α} (nd : A.Nodup) (nonempty : A ≠ [])
    (cov : Covers (· ∈ A) w) : ∃ a ∈ A, A.length ≤ w.count a := by sorry
