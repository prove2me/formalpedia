-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_idemFix_scottTopology
-- name    : Scott1972.ContinuousLattice.idemFix_scottTopology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:05.410931+00:00
-- url     : https://prove2.me/theorems/aeca2b68-ab39-4c80-ab43-a67a5e441732
-- title:
--   Continuous Lattice: idem Fix scott Topology
-- statement:
--   **Scott topology of the fixed-point lattice = subspace topology.** Proposition 2.10(b) applied
--   to `idemFixRetraction`: the Scott topology of `IdemFix e` is the topology induced by the inclusion
--   from the Scott topology of `L`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L160-L166
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L160-L166

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {L : Type*} [CompleteLattice L]
variable {e : L → L}

theorem Scott1972.ContinuousLattice.idemFix_scottTopology (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : IsContinuousLattice L) :
    @scottTopologicalSpace (IdemFix e)
        (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) =
      TopologicalSpace.induced (Subtype.val : IdemFix e → L) scottTopologicalSpace := by sorry
