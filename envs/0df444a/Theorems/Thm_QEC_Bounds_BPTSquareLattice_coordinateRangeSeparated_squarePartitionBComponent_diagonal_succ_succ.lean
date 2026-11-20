-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_squarePartitionBComponent_diagonal_succ_succ
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionBComponent_diagonal_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:28:35.285438+00:00
-- url     : https://prove2.me/theorems/2195a489-c977-4ece-9473-417e780bc228
-- title:
--   BPTSquare Lattice: coordinate Range Separated square Partition BComponent diagonal succ succ
-- statement:
--   The diagonal corner-cutout separation specialized to indexed `B` blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L883-L898
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L883-L898

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionBComponent_diagonal_succ_succ
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionBComponent blockWidth margin index)
      (L.squarePartitionBComponent blockWidth margin (index.1 + 1, index.2 + 1)) := by sorry
