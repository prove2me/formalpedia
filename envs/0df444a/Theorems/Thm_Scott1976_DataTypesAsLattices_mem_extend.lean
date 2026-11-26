-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_extend
-- name    : Scott1976.DataTypesAsLattices.mem_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:08.970884+00:00
-- url     : https://prove2.me/theorems/86eb0ec0-28b2-455b-a322-dd372b054702
-- title:
--   Data Types As Lattices: mem extend
-- statement:
--   The Data Types As Lattices construction uses the mem extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L28-L42
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L28-L42

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace

theorem Scott1976.DataTypesAsLattices.mem_extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) {y : Y} {k : ℕ} :
    k ∈ extend (Y := Y) (X := X) f y ↔
      ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x := by sorry
