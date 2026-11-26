-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_omega_first_recursion
-- name    : Scott1976.DataTypesAsLattices.omega_first_recursion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:52.913947+00:00
-- url     : https://prove2.me/theorems/aa139f9c-d21d-5f5b-9e4b-f190c9839f87
-- title:
--   Data Types As Lattices: omega first recursion
-- statement:
--   Scott's core induction proving that `ω(graph f)(ω(graph f))` is the
--   least fixed point of `f`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L466-L495
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L466-L495

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.omega_first_recursion {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (omegaComb (graph f)) (omegaComb (graph f)) = fix f := by sorry
