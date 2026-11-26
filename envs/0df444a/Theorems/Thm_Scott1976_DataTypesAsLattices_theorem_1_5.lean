-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_5
-- name    : Scott1976.DataTypesAsLattices.theorem_1_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:10.649166+00:00
-- url     : https://prove2.me/theorems/074a69d3-7212-5dcc-a281-8f16b97ea537
-- title:
--   Data Types As Lattices: theorem 1 5
-- statement:
--   **Scott 1976, Theorem 1.5 (The extension theorem), continuity.**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L61-L65
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L61-L65

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace

theorem Scott1976.DataTypesAsLattices.theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by sorry
