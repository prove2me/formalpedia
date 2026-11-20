-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_subset_expandedTile_of_subset_tile
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_subset_expandedTile_of_subset_tile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:18:56.394656+00:00
-- url     : https://prove2.me/theorems/380d8d96-71dd-4ab6-a809-a8e05718ddd6
-- title:
--   BPTCommuting Projector Model: external Boundary subset expanded Tile of subset tile
-- statement:
--   Every actual external-boundary site of a region contained in one tile lies in
--   the explicitly enlarged tile.  The proof uses the concrete support-coupling
--   witness and #378 square-locality, not a graph-neighbourhood surrogate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1531-L1575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1531-L1575

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_subset_expandedTile_of_subset_tile
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (index : Nat × Nat) (block : Finset L.Site)
    (hblock : block ⊆ L.lattice.tile blockWidth index)
    (hrange : M.interactionRange ≤ margin) :
    M.externalBoundary block ⊆ L.lattice.expandedTile blockWidth margin index := by sorry
