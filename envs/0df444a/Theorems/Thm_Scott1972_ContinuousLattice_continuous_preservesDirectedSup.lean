-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_continuous_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.continuous_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:38.650347+00:00
-- url     : https://prove2.me/theorems/6860dc3b-f769-56a6-9ed5-b45991ca24af
-- title:
--   Continuous Lattice: continuous preserves Directed Sup
-- statement:
--   The Continuous Lattice construction uses the continuous preserves Directed Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L59-L72
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L59-L72

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.continuous_preservesDirectedSup {f : D → D'}
    (hf : @Continuous D D' scottTopologicalSpace scottTopologicalSpace f) :
    PreservesDirectedSup f := by sorry
