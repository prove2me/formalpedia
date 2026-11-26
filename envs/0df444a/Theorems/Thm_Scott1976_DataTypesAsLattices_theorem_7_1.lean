-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_7_1
-- name    : Scott1976.DataTypesAsLattices.theorem_7_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:55.712044+00:00
-- url     : https://prove2.me/theorems/806253f4-0771-4d52-aa1d-c308082bd217
-- title:
--   Data Types As Lattices: theorem 7 1
-- statement:
--   **Scott 1976, Theorem 7.1 (The closure theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L92-L111
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L92-L111

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_7_1 (A B : RestrictedEquiv) :
    (∀ f, (arrowE A B).mem f →
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ u, (prodE A B).mem u →
        A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u →
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by sorry
