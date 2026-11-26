-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_pair_le_right
-- name    : Scott1976.DataTypesAsLattices.pair_le_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:32.053011+00:00
-- url     : https://prove2.me/theorems/03ebd8f9-1db6-428f-b4b9-a8b4b88fab89
-- title:
--   Data Types As Lattices: pair le right
-- statement:
--   The Data Types As Lattices construction uses the pair le right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L179-L180
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L179-L180

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.pair_le_right (n m : ℕ) : m ≤ pair n m := by sorry
