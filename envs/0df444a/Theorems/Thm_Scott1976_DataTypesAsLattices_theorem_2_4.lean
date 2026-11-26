-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_4
-- name    : Scott1976.DataTypesAsLattices.theorem_2_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:12.098411+00:00
-- url     : https://prove2.me/theorems/74a4ae18-c757-5347-b418-42d5f537f806
-- title:
--   Data Types As Lattices: theorem 2 4
-- statement:
--   **Scott 1976, Theorem 2.4 (The combinator theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L415-L417
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L415-L417

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb := by sorry
