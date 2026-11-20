-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_tileIndex_eq_of_mem_tile
-- name    : QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_tile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:16.282808+00:00
-- url     : https://prove2.me/theorems/928814db-f116-47a7-964b-9ebc17db16de
-- title:
--   BPTSquare Lattice: tile Index eq of mem tile
-- statement:
--   A site in an explicitly indexed tile has exactly that quotient pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L404-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L404-L413

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

theorem QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_tile (L : BPTSquareLattice) {blockWidth : Nat}
    (_hblockWidth : 0 < blockWidth) {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.tile blockWidth index) :
    L.tileIndex blockWidth site = index := by sorry
