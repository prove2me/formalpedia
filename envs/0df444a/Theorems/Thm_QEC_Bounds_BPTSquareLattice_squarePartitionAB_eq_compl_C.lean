-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionAB_eq_compl_C
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionAB_eq_compl_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:13.242971+00:00
-- url     : https://prove2.me/theorems/bf38f6d8-fcc1-4463-8f81-e1c8f9b373b3
-- title:
--   BPTSquare Lattice: square Partition AB eq compl C
-- statement:
--   The source `C` region is exactly the complement of the two checkerboard regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L993-L1002
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L993-L1002

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionAB_eq_compl_C (L : BPTSquareLattice)
    (blockWidth margin : Nat) :
    L.squarePartitionA blockWidth margin ∪ L.squarePartitionB blockWidth margin =
      (L.squarePartitionC blockWidth margin)ᶜ := by sorry
