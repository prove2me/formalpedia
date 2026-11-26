-- Prove2me | Theorems.Thm_Supersequence_cut
-- name    : Supersequence.cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:54.369153+00:00
-- url     : https://prove2.me/theorems/80af28af-2c3e-53fe-8081-5474e1756052
-- title:
--   Supersequence: cut
-- statement:
--   Any embedding chooses its pivot on one side of a pivot-free gap.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L32-L36
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L32-L36

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}

theorem Supersequence.cut {x : α} {u v l g r : List α} (hx : x ∉ g)
    (h : (u ++ x :: v).Sublist (l ++ (g ++ r))) : u.Sublist l ∨ v.Sublist r := by sorry
