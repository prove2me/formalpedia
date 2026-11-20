-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_tileIndex_eq_of_mem_squarePartitionBComponent
-- name    : QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_squarePartitionBComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:29:27.855219+00:00
-- url     : https://prove2.me/theorems/de14d2cb-f211-45c1-9d2c-fc4f5f80d600
-- title:
--   BPTSquare Lattice: tile Index eq of mem square Partition BComponent
-- statement:
--   A point in an indexed `B` component carries that component's exact tile index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L495-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L495-L501

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

theorem QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_squarePartitionBComponent (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.squarePartitionBComponent blockWidth margin index) :
    L.tileIndex blockWidth site = index := by sorry
