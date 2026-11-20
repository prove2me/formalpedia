-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_tileIndex_eq_of_mem_squarePartitionAComponent
-- name    : QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_squarePartitionAComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:27:50.872649+00:00
-- url     : https://prove2.me/theorems/26d3dd7a-178c-4e7c-8875-3a2325db1764
-- title:
--   BPTSquare Lattice: tile Index eq of mem square Partition AComponent
-- statement:
--   A point in an indexed `A` component carries that component's exact tile index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L486-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L486-L492

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

theorem QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_squarePartitionAComponent (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.squarePartitionAComponent blockWidth margin index) :
    L.tileIndex blockWidth site = index := by sorry
