-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone
-- name    : Scott1972.ContinuousLattice.preservesDirectedSup_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:31.422396+00:00
-- url     : https://prove2.me/theorems/749223c8-b5b1-5f40-9ad7-3ebc637f6115
-- title:
--   Continuous Lattice: preserves Directed Sup monotone
-- statement:
--   The Continuous Lattice construction uses the preserves Directed Sup monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L25-L35
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L25-L35

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.preservesDirectedSup_monotone {f : D → D'} (hf : PreservesDirectedSup f) :
    Monotone f := by sorry
