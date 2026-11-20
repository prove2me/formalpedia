-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartition_union_eq_univ
-- name    : QEC.Bounds.BPTSquareLattice.squarePartition_union_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:29:03.744205+00:00
-- url     : https://prove2.me/theorems/f73195ae-74b1-4de7-84e1-0c2e41d83bb4
-- title:
--   BPTSquare Lattice: square Partition union eq univ
-- statement:
--   The explicitly constructed `A`, `B`, and `C` regions cover the lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L981-L990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L981-L990

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

theorem QEC.Bounds.BPTSquareLattice.squarePartition_union_eq_univ (L : BPTSquareLattice)
    (blockWidth margin : Nat) :
    L.squarePartitionA blockWidth margin ∪ L.squarePartitionB blockWidth margin ∪
      L.squarePartitionC blockWidth margin = Finset.univ := by sorry
