-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:01.53265+00:00
-- url     : https://prove2.me/theorems/11484542-f20c-4b0b-82af-bc9ff168645c
-- title:
--   BPTSquare Lattice: coordinate Range Separated square Partition BComponent of odd distinct
-- statement:
--   Every two distinct odd-colored indexed `B` components have the source gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L842-L863
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L842-L863

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (leftIndex rightIndex : Nat × Nat)
    (hoddLeft : ¬ Even (leftIndex.1 + leftIndex.2))
    (hoddRight : ¬ Even (rightIndex.1 + rightIndex.2))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionBComponent blockWidth margin leftIndex)
      (L.squarePartitionBComponent blockWidth margin rightIndex) := by sorry
