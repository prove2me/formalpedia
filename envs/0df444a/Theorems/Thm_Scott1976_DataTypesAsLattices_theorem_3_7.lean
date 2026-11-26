-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_7
-- name    : Scott1976.DataTypesAsLattices.theorem_3_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:32.301611+00:00
-- url     : https://prove2.me/theorems/da70d5bf-b2b3-4140-b887-3873fd26fdc1
-- title:
--   Data Types As Lattices: theorem 3 7
-- statement:
--   **Scott 1976, Theorem 3.7 / (3.16).** `L` is the packed application combinator.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L155-L157
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L155-L157

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_7 :
    Lcomb = graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2))) := by sorry
