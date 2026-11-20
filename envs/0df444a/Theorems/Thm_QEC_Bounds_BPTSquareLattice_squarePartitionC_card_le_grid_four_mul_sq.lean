-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionC_card_le_grid_four_mul_sq
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionC_card_le_grid_four_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:04.499797+00:00
-- url     : https://prove2.me/theorems/848dd559-9ecd-4df2-a8d2-a48595ba8b73
-- title:
--   BPTSquare Lattice: square Partition C card le grid four mul sq
-- statement:
--   The finite C corner region has the explicit regular-grid bound
--   `4 * margin^2` per tile.  There is no asymptotic remainder hidden at an open
--   boundary: the row and column grid equalities are stated as hypotheses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1251-L1280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1251-L1280

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionC_card_le_grid_four_mul_sq (L : BPTSquareLattice)
    {blockWidth margin tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : margin ≤ blockWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.squarePartitionC blockWidth margin).card ≤
      tileRows * tileColumns * (4 * margin * margin) := by sorry
