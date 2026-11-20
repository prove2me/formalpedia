-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_tile_fits_of_mem_occupiedTileIndices_grid
-- name    : QEC.Bounds.BPTSquareLattice.tile_fits_of_mem_occupiedTileIndices_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:57.836362+00:00
-- url     : https://prove2.me/theorems/9cf7a1c6-1135-434e-9064-45d4ef344bc6
-- title:
--   BPTSquare Lattice: tile fits of mem occupied Tile Indices grid
-- statement:
--   Every occupied regular-grid tile is a fully present source square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1218-L1244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1218-L1244

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

theorem QEC.Bounds.BPTSquareLattice.tile_fits_of_mem_occupiedTileIndices_grid (L : BPTSquareLattice)
    {blockWidth tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth)
    (index : Nat × Nat) (hindex : index ∈ L.occupiedTileIndices blockWidth) :
    L.squareFits (index.1 * blockWidth, index.2 * blockWidth) blockWidth := by sorry
