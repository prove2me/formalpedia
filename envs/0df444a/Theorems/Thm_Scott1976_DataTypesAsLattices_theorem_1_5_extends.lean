-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_5_extends
-- name    : Scott1976.DataTypesAsLattices.theorem_1_5_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:13.933808+00:00
-- url     : https://prove2.me/theorems/9fec6c65-edba-4040-99ca-463858e67af4
-- title:
--   Data Types As Lattices: theorem 1 5 extends
-- statement:
--   **Scott 1976, Theorem 1.5**, extension property when `f` is continuous.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L68-L86
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L68-L86

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace

theorem Scott1976.DataTypesAsLattices.theorem_1_5_extends {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (hf : Continuous f) (x : X) :
    extend (Y := Y) (X := X) f ↑x = f x := by sorry
