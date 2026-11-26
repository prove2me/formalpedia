-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mu_law
-- name    : Scott1976.DataTypesAsLattices.mu_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:53.273615+00:00
-- url     : https://prove2.me/theorems/e8ddd41c-2fa8-4633-a359-054ce00b9716
-- title:
--   Data Types As Lattices: mu law
-- statement:
--   **Scott 1976, (μ).** Application is monotone in both arguments.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L48-L50
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L48-L50

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mu_law {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y := by sorry
