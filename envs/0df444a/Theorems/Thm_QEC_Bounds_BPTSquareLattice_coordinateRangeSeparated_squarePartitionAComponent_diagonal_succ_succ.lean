-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_squarePartitionAComponent_diagonal_succ_succ
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionAComponent_diagonal_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:29:10.695397+00:00
-- url     : https://prove2.me/theorems/59406a82-85b0-489b-a123-e587ba406d02
-- title:
--   BPTSquare Lattice: coordinate Range Separated square Partition AComponent diagonal succ succ
-- statement:
--   The diagonal corner-cutout separation specialized to indexed `A` blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L865-L880
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L865-L880

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionAComponent_diagonal_succ_succ
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionAComponent blockWidth margin index)
      (L.squarePartitionAComponent blockWidth margin (index.1 + 1, index.2 + 1)) := by sorry
