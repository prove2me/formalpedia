-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_squarePartitionAComponent_of_even_distinct
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionAComponent_of_even_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:34.629192+00:00
-- url     : https://prove2.me/theorems/83ea0208-62a0-4bd9-82f4-ce28819750fe
-- title:
--   BPTSquare Lattice: coordinate Range Separated square Partition AComponent of even distinct
-- statement:
--   Every two distinct even-colored indexed `A` components have the source gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L824-L839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L824-L839

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionAComponent_of_even_distinct
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (leftIndex rightIndex : Nat × Nat)
    (hevenLeft : Even (leftIndex.1 + leftIndex.2))
    (hevenRight : Even (rightIndex.1 + rightIndex.2))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionAComponent blockWidth margin leftIndex)
      (L.squarePartitionAComponent blockWidth margin rightIndex) := by sorry
