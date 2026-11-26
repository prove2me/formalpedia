-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_7_inf_right
-- name    : Scott1972.ContinuousLattice.proposition_2_7_inf_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:38.204064+00:00
-- url     : https://prove2.me/theorems/664a50c2-1ebc-5c25-ac56-b6f59bc7c603
-- title:
--   Continuous Lattice: proposition 2 7 inf right
-- statement:
--   The Continuous Lattice construction uses the proposition 2 7 inf right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L207-L209
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L207-L209

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.proposition_2_7_inf_right (hD : IsContinuousLattice D) (x : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun y => x ⊓ y) := by sorry
