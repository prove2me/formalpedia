-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_biUnion_squarePartitionAComponents_eq_squarePartitionA
-- name    : QEC.Bounds.BPTSquareLattice.biUnion_squarePartitionAComponents_eq_squarePartitionA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:39.43667+00:00
-- url     : https://prove2.me/theorems/ea1d96ae-1475-4f5d-bb1c-719c0e0223a4
-- title:
--   BPTSquare Lattice: bi Union square Partition AComponents eq square Partition A
-- statement:
--   The actual finite family of `A` blocks covers exactly the constructed `A` region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L901-L928
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L901-L928

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

theorem QEC.Bounds.BPTSquareLattice.biUnion_squarePartitionAComponents_eq_squarePartitionA
    (L : BPTSquareLattice) {blockWidth : Nat} (hblockWidth : 0 < blockWidth)
    (margin : Nat) :
    (L.squarePartitionAComponents blockWidth margin).biUnion id =
      L.squarePartitionA blockWidth margin := by sorry
