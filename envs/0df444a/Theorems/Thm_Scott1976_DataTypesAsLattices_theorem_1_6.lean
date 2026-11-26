-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_6
-- name    : Scott1976.DataTypesAsLattices.theorem_1_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:14.045513+00:00
-- url     : https://prove2.me/theorems/5fe2f3e0-7f86-4300-9dbd-f3ddc88011c3
-- title:
--   Data Types As Lattices: theorem 1 6
-- statement:
--   **Scott 1976, Theorem 1.6 (The embedding theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L93-L116
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean#L93-L116

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace

theorem Scott1976.DataTypesAsLattices.theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Function.Injective (embed U) ∧ Continuous (embed U) := by sorry
