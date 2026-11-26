-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_6
-- name    : Scott1972.ContinuousLattice.proposition_2_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:07.802656+00:00
-- url     : https://prove2.me/theorems/b609e0c3-5722-4301-a4d4-c8de5f9d2459
-- title:
--   Continuous Lattice: proposition 2 6
-- statement:
--   **Scott 1972, Proposition 2.6.** A function of several variables between complete lattices is
--   (Scott-)continuous jointly iff it is continuous in each variable separately. Continuity is phrased
--   as preservation of directed suprema (Proposition 2.5); it suffices to treat two variables, the
--   product `D × D'` carrying the componentwise complete-lattice structure (whose induced topology is
--   the product topology).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L87-L164
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L87-L164

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.proposition_2_6 (f : D × D' → D'') :
    PreservesDirectedSup f ↔
      (∀ y, PreservesDirectedSup fun x => f (x, y)) ∧
        (∀ x, PreservesDirectedSup fun y => f (x, y)) := by sorry
