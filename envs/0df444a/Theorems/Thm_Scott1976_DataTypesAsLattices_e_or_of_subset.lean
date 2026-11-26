-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_e_or_of_subset
-- name    : Scott1976.DataTypesAsLattices.e_or_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:49.388508+00:00
-- url     : https://prove2.me/theorems/2d15c1b9-3921-57f8-adf8-a5497b3a58a1
-- title:
--   Data Types As Lattices: e or of subset
-- statement:
--   The Data Types As Lattices construction uses the e or of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L91-L94
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L91-L94

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.e_or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by sorry
