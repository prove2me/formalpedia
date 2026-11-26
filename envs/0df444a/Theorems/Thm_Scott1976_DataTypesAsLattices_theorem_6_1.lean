-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_1
-- name    : Scott1976.DataTypesAsLattices.theorem_6_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:20.394742+00:00
-- url     : https://prove2.me/theorems/f4c6fcd4-a423-5951-818c-e1f77fda009b
-- title:
--   Data Types As Lattices: theorem 6 1
-- statement:
--   **Scott 1976, Theorem 6.1 (The 𝔊 theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L33-L60
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L33-L60

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by sorry
