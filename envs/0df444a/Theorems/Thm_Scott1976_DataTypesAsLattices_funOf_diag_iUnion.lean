-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_diag_iUnion
-- name    : Scott1976.DataTypesAsLattices.funOf_diag_iUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:57.46241+00:00
-- url     : https://prove2.me/theorems/22c132e1-6c9c-444b-b3aa-9ad6fd34afbd
-- title:
--   Data Types As Lattices: fun Of diag i Union
-- statement:
--   Appendix calculation: `d(d) = ⋃ { e_l(e_l) | e_l ⊆ d }`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L456-L462
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L456-L462

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.funOf_diag_iUnion (d : Pomega) :
    funOf d d = ⋃ l, {m | e l ⊆ d ∧ m ∈ funOf (e l) (e l)} := by sorry
