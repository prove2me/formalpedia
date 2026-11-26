-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_7_3_ii
-- name    : Scott1976.DataTypesAsLattices.theorem_7_3_ii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:13.349908+00:00
-- url     : https://prove2.me/theorems/aaa777c1-90c3-464e-b317-374f5b0b0938
-- title:
--   Data Types As Lattices: theorem 7 3 ii
-- statement:
--   **Scott 1976, Theorem 7.3 (ii).** `K` sends related arguments to
--   constant functions that remain related.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L165-L169
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L165-L169

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_7_3_ii (A B : RestrictedEquiv) {x x' : Pomega}
    (h : A.rel x x') :
    (arrowE B A).rel (funOf Kcomb x) (funOf Kcomb x') ∨
      A.rel x x' := by sorry
