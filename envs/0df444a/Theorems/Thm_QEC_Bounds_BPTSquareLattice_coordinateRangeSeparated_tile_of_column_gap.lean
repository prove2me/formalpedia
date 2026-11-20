-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_tile_of_column_gap
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_tile_of_column_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:20.078902+00:00
-- url     : https://prove2.me/theorems/7777e27a-ea34-472b-8f7a-6669d647dea1
-- title:
--   BPTSquare Lattice: coordinate Range Separated tile of column gap
-- statement:
--   Tiles with a full tile between them in the column direction have the requested gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L545-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L545-L562

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_tile_of_column_gap (L : BPTSquareLattice)
    {blockWidth range : Nat} (hrange : range ≤ blockWidth)
    (leftIndex rightIndex : Nat × Nat) (hcolumn : leftIndex.2 + 1 < rightIndex.2) :
    L.CoordinateRangeSeparated range (L.tile blockWidth leftIndex)
      (L.tile blockWidth rightIndex) := by sorry
