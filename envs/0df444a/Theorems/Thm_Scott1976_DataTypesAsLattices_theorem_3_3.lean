-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_3
-- name    : Scott1976.DataTypesAsLattices.theorem_3_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:10.690587+00:00
-- url     : https://prove2.me/theorems/21784353-7396-54e6-8c4b-203e42f71fc3
-- title:
--   Data Types As Lattices: theorem 3 3
-- statement:
--   The Data Types As Lattices construction uses the theorem 3 3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L69-L70
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L69-L70

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_3 (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := by sorry
