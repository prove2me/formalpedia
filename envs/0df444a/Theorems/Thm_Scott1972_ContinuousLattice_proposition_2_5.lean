-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_5
-- name    : Scott1972.ContinuousLattice.proposition_2_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:41.224024+00:00
-- url     : https://prove2.me/theorems/739a7f43-5ff6-487e-ba47-096be6403b4f
-- title:
--   Continuous Lattice: proposition 2 5
-- statement:
--   **Scott 1972, Proposition 2.5.** Scott continuity ↔ preservation of directed suprema.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L75-L78
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L75-L78

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.proposition_2_5 (f : D → D') :
    (@Continuous D D' scottTopologicalSpace scottTopologicalSpace f) ↔
      PreservesDirectedSup f := by sorry
