-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_graph_ext
-- name    : Scott1976.DataTypesAsLattices.graph_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:07.431087+00:00
-- url     : https://prove2.me/theorems/1d089810-2413-419e-ac6a-72e193caa763
-- title:
--   Data Types As Lattices: graph ext
-- statement:
--   The Data Types As Lattices construction uses the graph ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L187-L189
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L187-L189

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.graph_ext {f g : Pomega → Pomega} (h : ∀ x, f x = g x) :
    graph f = graph g := by sorry
