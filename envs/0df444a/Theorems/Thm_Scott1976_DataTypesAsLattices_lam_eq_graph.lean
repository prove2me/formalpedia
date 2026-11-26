-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_lam_eq_graph
-- name    : Scott1976.DataTypesAsLattices.lam_eq_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:05.127897+00:00
-- url     : https://prove2.me/theorems/900d46fb-ee57-402c-bab8-0f852aaa84b8
-- title:
--   Data Types As Lattices: lam eq graph
-- statement:
--   The Data Types As Lattices construction uses the lam eq graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L119-L119
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L119-L119

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.lam_eq_graph (τ : Pomega → Pomega) : lam τ = graph τ := by sorry
