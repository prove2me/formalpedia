-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_singleton_eq_e
-- name    : Scott1976.DataTypesAsLattices.singleton_eq_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:22.255134+00:00
-- url     : https://prove2.me/theorems/d01d4ff0-b2fb-48e5-8cd8-28532d7f011f
-- title:
--   Data Types As Lattices: singleton eq e
-- statement:
--   The Data Types As Lattices construction uses the singleton eq e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L67-L67
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L67-L67

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.singleton_eq_e (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := by sorry
