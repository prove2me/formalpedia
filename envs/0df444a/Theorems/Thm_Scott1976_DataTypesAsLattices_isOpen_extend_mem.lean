-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_isOpen_extend_mem
-- name    : Scott1976.DataTypesAsLattices.isOpen_extend_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:16.065688+00:00
-- url     : https://prove2.me/theorems/99ba3cb4-57fc-534c-9f52-3a05c45e073f
-- title:
--   Data Types As Lattices: is Open extend mem
-- statement:
--   The Data Types As Lattices construction uses the is Open extend mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L44-L58
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L44-L58

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace

theorem Scott1976.DataTypesAsLattices.isOpen_extend_mem {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (k : ℕ) :
    IsOpen {y : Y | k ∈ extend (Y := Y) (X := X) f y} := by sorry
