-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.continuous_of_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:35.550514+00:00
-- url     : https://prove2.me/theorems/470274af-9d0a-42e6-9c00-7d21885c252b
-- title:
--   Continuous Lattice: continuous of preserves Directed Sup
-- statement:
--   The Continuous Lattice construction uses the continuous of preserves Directed Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L52-L57
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L52-L57

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.continuous_of_preservesDirectedSup {f : D → D'} (hf : PreservesDirectedSup f) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f := by sorry
