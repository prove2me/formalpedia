-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_6
-- name    : Scott1976.DataTypesAsLattices.theorem_4_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:32.198067+00:00
-- url     : https://prove2.me/theorems/06759cad-c4be-493e-b754-98faef1da449
-- title:
--   Data Types As Lattices: theorem 4 6
-- statement:
--   **Scott 1976, Theorem 4.6 (The limit theorem).**
--   Each Kleene iterate `Fⁿ(⊥)` is a retract when `F` preserves retracts.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L289-L293
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L289-L293

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_6 {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    ∀ n, IsRetract (iterateBot F n)
  := by sorry
