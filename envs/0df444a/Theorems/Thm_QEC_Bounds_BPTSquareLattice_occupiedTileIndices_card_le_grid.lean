-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_occupiedTileIndices_card_le_grid
-- name    : QEC.Bounds.BPTSquareLattice.occupiedTileIndices_card_le_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:44.646114+00:00
-- url     : https://prove2.me/theorems/4332bb81-a3b8-4ce5-a4e5-eb9b52f8bab1
-- title:
--   BPTSquare Lattice: occupied Tile Indices card le grid
-- statement:
--   A finite regular `blockWidth` tiling has at most its declared grid many occupied tiles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1184-L1215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1184-L1215

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

theorem QEC.Bounds.BPTSquareLattice.occupiedTileIndices_card_le_grid (L : BPTSquareLattice)
    {blockWidth tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.occupiedTileIndices blockWidth).card ≤ tileRows * tileColumns := by sorry
