-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_4_ii
-- name    : Scott1976.DataTypesAsLattices.theorem_4_4_ii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:19.710877+00:00
-- url     : https://prove2.me/theorems/fa9c2581-d01b-4b00-81d9-353857e0aa30
-- title:
--   Data Types As Lattices: theorem 4 4 ii
-- statement:
--   **Scott 1976, Theorem 4.4 (ii), pairing form.** A pair-as-function
--   projects to its components.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L265-L268
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L265-L268

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_4_ii (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y := by sorry
