-- Prove2me | Theorems.Thm_Supersequence_outerCutLength
-- name    : Supersequence.outerCutLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:09:46.539937+00:00
-- url     : https://prove2.me/theorems/78f6a89d-4e79-46f3-b553-d3ce80f67268
-- title:
--   Supersequence: outer Cut Length
-- statement:
--   A complementary cut on nine old letters with first side of length at most
--   12 requires at least 50 positions on the other side.
--
--   Source: https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L225-L263
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean#L225-L263

import Definitions.Def_Frequency
import Definitions.Def_Four
set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]

theorem Supersequence.outerCutLength {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 12) (cutOK : Compatible A p q)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) : 50 ≤ q.length := by sorry
