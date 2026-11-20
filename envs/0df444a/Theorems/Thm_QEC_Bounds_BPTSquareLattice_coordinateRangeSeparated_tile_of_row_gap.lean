-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_tile_of_row_gap
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_tile_of_row_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:22:46.292188+00:00
-- url     : https://prove2.me/theorems/4d1976d0-9ff3-4338-9583-a9b55b04eb08
-- title:
--   BPTSquare Lattice: coordinate Range Separated tile of row gap
-- statement:
--   Tiles with a full tile between them in the row direction have the requested gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L525-L542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L525-L542

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_tile_of_row_gap (L : BPTSquareLattice)
    {blockWidth range : Nat} (hrange : range ≤ blockWidth)
    (leftIndex rightIndex : Nat × Nat) (hrow : leftIndex.1 + 1 < rightIndex.1) :
    L.CoordinateRangeSeparated range (L.tile blockWidth leftIndex)
      (L.tile blockWidth rightIndex) := by sorry
