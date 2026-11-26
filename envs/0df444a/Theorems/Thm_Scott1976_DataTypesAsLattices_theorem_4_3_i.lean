-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_3_i
-- name    : Scott1976.DataTypesAsLattices.theorem_4_3_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:17.773498+00:00
-- url     : https://prove2.me/theorems/83bb278b-6ba8-5aa1-ad8b-73ec894925d9
-- title:
--   Data Types As Lattices: theorem 4 3 i
-- statement:
--   **Scott 1976, Theorem 4.3 (i).** On elements, `a ∘→ b` acts as `b ∘ − ∘ a`,
--   and that action is idempotent when `a, b` are retracts.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L211-L216
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L211-L216

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_3_i {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    funOf (arrowR a b) (funOf (arrowR a b) u) = funOf (arrowR a b) u := by sorry
