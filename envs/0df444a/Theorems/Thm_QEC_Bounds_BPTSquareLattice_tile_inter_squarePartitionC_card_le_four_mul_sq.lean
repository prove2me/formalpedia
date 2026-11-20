-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_tile_inter_squarePartitionC_card_le_four_mul_sq
-- name    : QEC.Bounds.BPTSquareLattice.tile_inter_squarePartitionC_card_le_four_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:53.559823+00:00
-- url     : https://prove2.me/theorems/c5decd63-ff77-465d-a389-b4ee4bc02b10
-- title:
--   BPTSquare Lattice: tile inter square Partition C card le four mul sq
-- statement:
--   A single source tile contributes at most four `margin`-squared C sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1114-L1181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1114-L1181

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

theorem QEC.Bounds.BPTSquareLattice.tile_inter_squarePartitionC_card_le_four_mul_sq (L : BPTSquareLattice)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth) (hmargin : margin ≤ blockWidth)
    (index : Nat × Nat) :
    (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card ≤
      4 * margin * margin := by sorry
