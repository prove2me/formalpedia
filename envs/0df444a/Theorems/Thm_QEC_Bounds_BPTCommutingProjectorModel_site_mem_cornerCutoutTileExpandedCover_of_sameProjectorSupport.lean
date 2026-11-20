-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_site_mem_cornerCutoutTileExpandedCover_of_sameProjectorSupport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.site_mem_cornerCutoutTileExpandedCover_of_sameProjectorSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:34.621597+00:00
-- url     : https://prove2.me/theorems/bd5ab9a0-15a6-4a3f-bff7-65b580acf6f9
-- title:
--   BPTCommuting Projector Model: site mem corner Cutout Tile Expanded Cover of same Projector Support
-- statement:
--   Any site in the same actual local-projector support as a tile-C corner lies in
--   the corresponding finite `3w` corner enlargement.  This is a support witness
--   calculation, not a graph-neighborhood replacement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1740-L1793
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1740-L1793

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

theorem QEC.Bounds.BPTCommutingProjectorModel.site_mem_cornerCutoutTileExpandedCover_of_sameProjectorSupport
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (hblockWidth : 0 < blockWidth) (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth) (index : Nat × Nat) (check : kappa)
    (cornerSite site : L.Site)
    (hcorner : cornerSite ∈
      L.lattice.tile blockWidth index ∩ L.lattice.squarePartitionC blockWidth margin)
    (hcornerSupport : cornerSite ∈ M.support check) (hsiteSupport : site ∈ M.support check) :
    site ∈ L.lattice.cornerCutoutTileExpandedCover blockWidth margin index := by sorry
