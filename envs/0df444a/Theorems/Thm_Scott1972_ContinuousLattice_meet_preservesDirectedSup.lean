-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_meet_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.meet_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:41.135232+00:00
-- url     : https://prove2.me/theorems/ef2b0957-b23a-514e-948f-2a800df89d0a
-- title:
--   Continuous Lattice: meet preserves Directed Sup
-- statement:
--   The Continuous Lattice construction uses the meet preserves Directed Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L176-L194
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L176-L194

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.meet_preservesDirectedSup (x : D) (hD : IsContinuousLattice D) :
    PreservesDirectedSup (fun z => x ⊓ z) := by sorry
