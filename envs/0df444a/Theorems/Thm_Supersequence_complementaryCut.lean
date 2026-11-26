-- Prove2me | Theorems.Thm_Supersequence_complementaryCut
-- name    : Supersequence.complementaryCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:16.04674+00:00
-- url     : https://prove2.me/theorems/32d2c223-cbf7-5ce2-a6bd-3ee544dbec17
-- title:
--   Supersequence: complementary Cut
-- statement:
--   Complementary alphabets cannot both have a missing order.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L39-L50
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L39-L50

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}

theorem Supersequence.complementaryCut {x : α} {l g r : List α} (hx : x ∉ g)
    (univ : Covers (fun _ => True) (l ++ (g ++ r))) (S : α → Prop) :
    Covers (fun a => a ≠ x ∧ S a) l ∨ Covers (fun a => a ≠ x ∧ ¬ S a) r := by sorry
