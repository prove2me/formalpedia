-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_occupiedTileIndices_card_le_openGrid
-- name    : QEC.Bounds.BPTSquareLattice.occupiedTileIndices_card_le_openGrid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:35.494948+00:00
-- url     : https://prove2.me/theorems/e44bc3a2-9c15-401d-a68d-5861e586a203
-- title:
--   BPTSquare Lattice: occupied Tile Indices card le open Grid
-- statement:
--   The open-boundary grid needs no divisibility hypothesis: every occupied tile
--   index lies below the quotient count of the last lattice coordinate plus one.
--   The positive side-length assumptions on `BPTSquareLattice` make this the exact
--   finite ceiling count, including a clipped final row or column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1288-L1327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1288-L1327

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

theorem QEC.Bounds.BPTSquareLattice.occupiedTileIndices_card_le_openGrid (L : BPTSquareLattice)
    (blockWidth : Nat) :
    (L.occupiedTileIndices blockWidth).card ≤
      ((L.rows - 1) / blockWidth + 1) * ((L.columns - 1) / blockWidth + 1) := by sorry
