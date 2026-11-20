-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_union_cornerCutoutTileExpandedCover_card_le_thirtyfour_mul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_union_cornerCutoutTileExpandedCover_card_le_thirtyfour_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:47.771897+00:00
-- url     : https://prove2.me/theorems/778dcc31-e5bd-4c2d-8b34-cef7061df733
-- title:
--   BPTCommuting Projector Model: boundary union corner Cutout Tile Expanded Cover card le thirtyfour mul
-- statement:
--   The previous support cover has the explicit source-scale finite bound
--   `34 * w * R`: `16*w*R` for the full-tile boundary and at most
--   `36*w^2 <= 18*w*R` for the four enlarged corners.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1841-L1869
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1841-L1869

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_union_cornerCutoutTileExpandedCover_card_le_thirtyfour_mul
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth) (index : Nat × Nat) :
    (M.boundary (L.lattice.tile blockWidth index) ∪
      L.lattice.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
        34 * margin * blockWidth := by sorry
