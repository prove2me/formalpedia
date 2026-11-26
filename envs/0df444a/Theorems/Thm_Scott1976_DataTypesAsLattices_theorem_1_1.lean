-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_1
-- name    : Scott1976.DataTypesAsLattices.theorem_1_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:56.532947+00:00
-- url     : https://prove2.me/theorems/6c413181-59ab-55aa-9466-1b0328717327
-- title:
--   Data Types As Lattices: theorem 1 1
-- statement:
--   **Scott 1976, Theorem 1.1 (The characterization theorem).**
--   `f` is continuous iff `e m ⊆ f(x)` just when some finite `e n ⊆ x` already
--   satisfies `e m ⊆ f(e n)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L88-L122
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L88-L122

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_1 (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by sorry
