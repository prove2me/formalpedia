-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_3
-- name    : Scott1976.DataTypesAsLattices.theorem_4_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:15.165815+00:00
-- url     : https://prove2.me/theorems/c9242b65-d830-4f20-a7ab-f5534bc208f5
-- title:
--   Data Types As Lattices: theorem 4 3
-- statement:
--   **Scott 1976, Theorem 4.3 (i).** Function spaces of retracts are retracts.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L238-L244
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L238-L244

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_3 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (arrowR a b) := by sorry
