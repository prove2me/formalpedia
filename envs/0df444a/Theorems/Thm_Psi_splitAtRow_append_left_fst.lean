-- Prove2me | Theorems.Thm_Psi_splitAtRow_append_left_fst
-- name    : Psi.splitAtRow_append_left_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:00.517333+00:00
-- url     : https://prove2.me/theorems/dd99cfcc-c3c4-4ce5-9c7f-11506c240cf8
-- title:
--   Psi: split At Row append left fst
-- statement:
--   When `B` ends in an East step and `h ≤ #North(B)`, the split of `B ++ C` at
--   row `h` completes inside `B`, so its first piece is exactly the split of `B`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L201-L229
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L201-L229

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_append_left_fst (B C : List Bool) (h : ℕ)
    (hend : stEast B false = true) (hh : h ≤ numN B) :
    (splitAtRow (B ++ C) h).1 = (splitAtRow B h).1 := by sorry
