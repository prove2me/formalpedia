-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionC_card_le_openGrid_four_mul_sq
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionC_card_le_openGrid_four_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:52.370177+00:00
-- url     : https://prove2.me/theorems/452ebbda-60e2-4ecb-ae0f-b626900a263f
-- title:
--   BPTSquare Lattice: square Partition C card le open Grid four mul sq
-- statement:
--   The finite `C` count for a clipped open-boundary grid.  Unlike the earlier
--   regular-grid lemma, it counts the partial final row and column explicitly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1333-L1362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1333-L1362

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionC_card_le_openGrid_four_mul_sq (L : BPTSquareLattice)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : margin ≤ blockWidth) :
    (L.squarePartitionC blockWidth margin).card ≤
      (((L.rows - 1) / blockWidth + 1) * ((L.columns - 1) / blockWidth + 1)) *
        (4 * margin * margin) := by sorry
