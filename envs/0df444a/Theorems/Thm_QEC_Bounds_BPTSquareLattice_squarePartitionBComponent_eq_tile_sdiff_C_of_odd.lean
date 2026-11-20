-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionBComponent_eq_tile_sdiff_C_of_odd
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:38.759171+00:00
-- url     : https://prove2.me/theorems/d9cea6d4-1349-4e32-aeb7-672fe5d0d958
-- title:
--   BPTSquare Lattice: square Partition BComponent eq tile sdiff C of odd
-- statement:
--   An odd tile's B component is exactly that tile with its C corners removed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L459-L483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L459-L483

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    (index : Nat × Nat) (hodd : ¬ Even (index.1 + index.2)) :
    L.squarePartitionBComponent blockWidth margin index =
      L.tile blockWidth index \ L.squarePartitionC blockWidth margin := by sorry
