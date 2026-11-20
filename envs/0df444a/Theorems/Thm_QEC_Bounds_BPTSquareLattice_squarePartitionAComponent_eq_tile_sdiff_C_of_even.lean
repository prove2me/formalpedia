-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionAComponent_eq_tile_sdiff_C_of_even
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:28.584974+00:00
-- url     : https://prove2.me/theorems/2ac545de-e06c-48ff-871f-b0d7902b4ec8
-- title:
--   BPTSquare Lattice: square Partition AComponent eq tile sdiff C of even
-- statement:
--   An even tile's A component is exactly that tile with its C corners removed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L432-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L432-L456

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    (index : Nat × Nat) (heven : Even (index.1 + index.2)) :
    L.squarePartitionAComponent blockWidth margin index =
      L.tile blockWidth index \ L.squarePartitionC blockWidth margin := by sorry
