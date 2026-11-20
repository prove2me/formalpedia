-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_tile_of_pos
-- name    : QEC.Bounds.BPTSquareLattice.mem_tile_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:11.590088+00:00
-- url     : https://prove2.me/theorems/24b74439-6371-48f8-b758-a6a0faea7082
-- title:
--   BPTSquare Lattice: mem tile of pos
-- statement:
--   Every site belongs to its explicitly indexed source square block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L379-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L379-L401

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

theorem QEC.Bounds.BPTSquareLattice.mem_tile_of_pos (L : BPTSquareLattice) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (site : L.Site) :
    site ∈ L.tile blockWidth (L.tileIndex blockWidth site) := by sorry
