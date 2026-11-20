-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_tile_sdiff_squarePartitionC_subset_boundary_union_cornerCover
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_tile_sdiff_squarePartitionC_subset_boundary_union_cornerCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:20.196422+00:00
-- url     : https://prove2.me/theorems/5bd3a822-eb50-4bc6-8dcc-454f63d3db59
-- title:
--   BPTCommuting Projector Model: external Boundary tile sdiff square Partition C subset boundary union corner Cover
-- statement:
--   The external boundary of a tile with its C corners removed is covered by the
--   tile's actual thin boundary plus the four enlarged C corners.  This preserves
--   the exact support-coupling witnesses needed by #403.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1800-L1834
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1800-L1834

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

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_tile_sdiff_squarePartitionC_subset_boundary_union_cornerCover
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (hblockWidth : 0 < blockWidth) (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth) (index : Nat × Nat) :
    M.externalBoundary
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin) ⊆
        M.boundary (L.lattice.tile blockWidth index) ∪
          L.lattice.cornerCutoutTileExpandedCover blockWidth margin index := by sorry
