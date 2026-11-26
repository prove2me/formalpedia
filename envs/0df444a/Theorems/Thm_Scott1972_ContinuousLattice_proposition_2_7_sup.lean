-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_7_sup
-- name    : Scott1972.ContinuousLattice.proposition_2_7_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:39.148803+00:00
-- url     : https://prove2.me/theorems/8a91ee4c-8a81-4721-984e-02afa3ac6eec
-- title:
--   Continuous Lattice: proposition 2 7 sup
-- statement:
--   **Scott 1972, Proposition 2.7 (join).** Binary join is Scott-continuous on every complete
--   lattice; this is the `⊔`-part of Scott's 2.7.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L170-L174
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L170-L174

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.proposition_2_7_sup :
    @Continuous (D × D) D scottTopologicalSpace scottTopologicalSpace (fun p : D × D => p.1 ⊔ p.2) := by sorry
