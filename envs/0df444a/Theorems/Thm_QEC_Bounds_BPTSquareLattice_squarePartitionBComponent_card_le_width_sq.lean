-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionBComponent_card_le_width_sq
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionBComponent_card_le_width_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:28.144832+00:00
-- url     : https://prove2.me/theorems/ad3addb4-8219-46dc-86b9-9fc955863334
-- title:
--   BPTSquare Lattice: square Partition BComponent card le width sq
-- statement:
--   Every `B` component is a finite source square truncated by the `C` cutout.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1056-L1063
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1056-L1063

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionBComponent_card_le_width_sq (L : BPTSquareLattice)
    (blockWidth margin : Nat) (block : Finset L.Site)
    (hblock : block ∈ L.squarePartitionBComponents blockWidth margin) :
    block.card <= blockWidth * blockWidth := by sorry
