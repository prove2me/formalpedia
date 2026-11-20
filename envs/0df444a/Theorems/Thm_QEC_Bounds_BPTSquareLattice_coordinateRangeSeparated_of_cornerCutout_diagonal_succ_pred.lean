-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:28.7442+00:00
-- url     : https://prove2.me/theorems/d74d76d8-5f83-4cc8-93cc-12c72d40ac64
-- title:
--   BPTSquare Lattice: coordinate Range Separated of corner Cutout diagonal succ pred
-- statement:
--   The other diagonal orientation is separated by the same corner cutout.  Here
--   the left region is in the upper-left tile and the right region in the
--   lower-right tile, so the two failed gaps force the upper-left point into its
--   lower-right removed corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L640-L705
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L640-L705

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
open QEC.Bounds.BPTSquareLattice

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) (left right : Finset L.Site)
    (hleftTile : left ⊆ L.tile blockWidth (index.1, index.2 + 1))
    (hleftNotCorner : ∀ site ∈ left, ¬ L.cornerCutout blockWidth margin site)
    (hrightTile : right ⊆ L.tile blockWidth (index.1 + 1, index.2)) :
    L.CoordinateRangeSeparated range left right := by sorry
