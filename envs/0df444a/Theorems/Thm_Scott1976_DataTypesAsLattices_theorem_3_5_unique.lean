-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_5_unique
-- name    : Scott1976.DataTypesAsLattices.theorem_3_5_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:10.163181+00:00
-- url     : https://prove2.me/theorems/04eeed23-8076-59b8-9bae-cb6c26fa826e
-- title:
--   Data Types As Lattices: theorem 3 5 unique
-- statement:
--   **Scott 1976, Theorem 3.5 (uniqueness half).** A continuous realizer of
--   an extensional map is unique, because continuous maps are determined by
--   their values on finite sets.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L117-L122
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L117-L122

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_5_unique {q q' : Pomega → Pomega}
    (hq : IsScottContinuous q) (hq' : IsScottContinuous q')
    (h : ∀ n, q (e n) = q' (e n)) (x : Pomega) : q x = q' x := by sorry
