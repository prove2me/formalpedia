-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_e_or
-- name    : Scott1976.DataTypesAsLattices.e_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:47.126191+00:00
-- url     : https://prove2.me/theorems/c003fd99-86e1-5a7c-9754-da82e2451cec
-- title:
--   Data Types As Lattices: e or
-- statement:
--   The Data Types As Lattices construction uses the e or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L87-L89
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L87-L89

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.e_or (n m : ℕ) : e (n ||| m) = e n ∪ e m := by sorry
