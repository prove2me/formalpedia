-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_7_3_iii
-- name    : Scott1976.DataTypesAsLattices.theorem_7_3_iii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:12.876904+00:00
-- url     : https://prove2.me/theorems/9bac82aa-f761-4c63-ab3d-2e0cf466ee38
-- title:
--   Data Types As Lattices: theorem 7 3 iii
-- statement:
--   **Scott 1976, Theorem 7.3 (iii).** The `S` combinator is defined so that
--   `S(f)(g)(x)` is intended to be `f(x)(g(x))`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L173-L176
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L173-L176

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_7_3_iii :
    Scomb = graph (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) := by sorry
