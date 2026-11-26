-- Prove2me | Theorems.Thm_Supersequence_bridge
-- name    : Supersequence.bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:58.642014+00:00
-- url     : https://prove2.me/theorems/aac67e2f-84c6-550d-b6a8-40140d6799a6
-- title:
--   Supersequence: bridge
-- statement:
--   Replace a pivot-free gap by one copy of each old letter. Greedily extend
--   the request on the left, then use the first failed letter in the bridge.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L59-L82
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean#L59-L82

import Std
import Definitions.Def_Frequency
set_option autoImplicit true
open Supersequence
open List
variable {α : Type}

theorem Supersequence.bridge {x : α} {l g r alphabet : List α} (hx : x ∉ g)
    (letters : ∀ a, a ≠ x → a ∈ alphabet)
    (h : Covers (fun _ => True) (l ++ (g ++ r))) :
    Covers (fun a => a ≠ x) (l ++ (alphabet ++ r)) := by sorry
