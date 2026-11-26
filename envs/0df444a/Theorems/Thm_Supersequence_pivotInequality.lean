-- Prove2me | Theorems.Thm_Supersequence_pivotInequality
-- name    : Supersequence.pivotInequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:11.174377+00:00
-- url     : https://prove2.me/theorems/bca703e0-8038-594b-a22b-9d8356ca1454
-- title:
--   Supersequence: pivot Inequality
-- statement:
--   If r copies leave t old letters, then F+m ≤ r*(t-F+m), with F a
--   lower bound on the old alphabet and m the length of a list containing it.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L177-L220
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L177-L220

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]

theorem Supersequence.pivotInequality {w alphabet : List α} {x : α} {F : Nat}
    (hw : Covers (fun _ => True) w) (low : LowerOnOthers x F)
    (letters : ∀ a, a ≠ x → a ∈ alphabet) :
    F + alphabet.length ≤ w.count x * ((project x w).length - F + alphabet.length) := by sorry
