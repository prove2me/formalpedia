-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_5_strict
-- name    : Scott1976.DataTypesAsLattices.theorem_4_5_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:32.28097+00:00
-- url     : https://prove2.me/theorems/b12c49ad-c668-44d5-8718-02fcc97530c6
-- title:
--   Data Types As Lattices: theorem 4 5 strict
-- statement:
--   **Scott 1976, Theorem 4.5 (i), strictness of sums.** The zero summand
--   is always selected on `⊥`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L272-L277
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L272-L277

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_5_strict (a b : Pomega) :
    condSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem := by sorry
