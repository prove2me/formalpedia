-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartition_pairwise_disjoint
-- name    : QEC.Bounds.BPTSquareLattice.squarePartition_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:03.049844+00:00
-- url     : https://prove2.me/theorems/a5b96cf4-7544-45ad-b896-caa08ecddf28
-- title:
--   BPTSquare Lattice: square Partition pairwise disjoint
-- statement:
--   The finite BPT regions are disjoint in the `A`, `B`, `C` source split.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L961-L978
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L961-L978

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

theorem QEC.Bounds.BPTSquareLattice.squarePartition_pairwise_disjoint (L : BPTSquareLattice)
    (blockWidth margin : Nat) :
    Disjoint (L.squarePartitionA blockWidth margin) (L.squarePartitionB blockWidth margin) ∧
      Disjoint (L.squarePartitionA blockWidth margin) (L.squarePartitionC blockWidth margin) ∧
        Disjoint (L.squarePartitionB blockWidth margin) (L.squarePartitionC blockWidth margin) := by sorry
