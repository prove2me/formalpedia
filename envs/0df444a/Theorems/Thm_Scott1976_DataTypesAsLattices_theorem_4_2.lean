-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_2
-- name    : Scott1976.DataTypesAsLattices.theorem_4_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:24.314005+00:00
-- url     : https://prove2.me/theorems/14619e80-9ec1-4147-8974-e00b1edaccc0
-- title:
--   Data Types As Lattices: theorem 4 2
-- statement:
--   **Scott 1976, Theorem 4.2 (The partial ordering theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L106-L114
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L106-L114

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_2 {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by sorry
