-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:36.962623+00:00
-- url     : https://prove2.me/theorems/1f762932-496a-4609-a7cd-d425dbca0ada
-- title:
--   BPTSquare Lattice: coordinate Range Separated of corner Cutout diagonal succ succ
-- statement:
--   The source corner cutout separates a tile from the diagonally next tile.  If
--   both coordinate gaps were smaller than `range`, the point in the lower-left
--   tile would lie in its removed corner window.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L569-L632
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L569-L632

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) (left right : Finset L.Site)
    (hleftTile : left ⊆ L.tile blockWidth index)
    (hleftNotCorner : ∀ site ∈ left, ¬ L.cornerCutout blockWidth margin site)
    (hrightTile : right ⊆ L.tile blockWidth (index.1 + 1, index.2 + 1)) :
    L.CoordinateRangeSeparated range left right := by sorry
