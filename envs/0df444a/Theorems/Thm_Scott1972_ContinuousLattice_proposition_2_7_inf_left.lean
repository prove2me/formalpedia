-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_7_inf_left
-- name    : Scott1972.ContinuousLattice.proposition_2_7_inf_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:35.599483+00:00
-- url     : https://prove2.me/theorems/e602b60b-fdde-50a0-b57a-58a17a50d505
-- title:
--   Continuous Lattice: proposition 2 7 inf left
-- statement:
--   **Scott 1972, Proposition 2.7 (meet, separate).** On a continuous lattice, `x ↦ x ⊓ y`
--   and `y ↦ x ⊓ y` are Scott-continuous; Scott's full 2.7 also covers joint continuity on the
--   product via Proposition 2.6.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L199-L205
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L199-L205

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.proposition_2_7_inf_left (hD : IsContinuousLattice D) (y : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun x => x ⊓ y) := by sorry
