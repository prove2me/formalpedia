-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_6
-- name    : Scott1976.DataTypesAsLattices.theorem_2_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:51.976253+00:00
-- url     : https://prove2.me/theorems/9d67b2a6-70b0-5f13-83b4-92d2c4caa575
-- title:
--   Data Types As Lattices: theorem 2 6
-- statement:
--   **Scott 1976, Theorem 2.6 (i) ↔ (ii).**
--   `f` is computable iff `λx. f(x)` (i.e. `graph f`) is r.e.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean#L35-L41
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean#L35-L41

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    IsComputable f ↔ IsRE (graph f) := by sorry
