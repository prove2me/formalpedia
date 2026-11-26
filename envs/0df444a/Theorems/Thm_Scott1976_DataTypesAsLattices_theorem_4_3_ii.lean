-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_3_ii
-- name    : Scott1976.DataTypesAsLattices.theorem_4_3_ii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:02.872989+00:00
-- url     : https://prove2.me/theorems/78b87daf-bead-496c-9dab-c6037bd73f04
-- title:
--   Data Types As Lattices: theorem 4 3 ii
-- statement:
--   **Scott 1976, Theorem 4.3 (ii).** `u : a ∘→ b` means `u` is restricted
--   to `a` and takes values in `b`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L226-L235
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L226-L235

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_3_ii {a b u x : Pomega}
    (hu : typed u (arrowR a b)) (hx : typed x a) :
    typed (funOf u x) b := by sorry
