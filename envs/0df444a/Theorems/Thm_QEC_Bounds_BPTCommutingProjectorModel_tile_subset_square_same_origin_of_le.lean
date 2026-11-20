-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tile_subset_square_same_origin_of_le
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tile_subset_square_same_origin_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:31.822178+00:00
-- url     : https://prove2.me/theorems/18aadaf5-519b-4b97-9508-112c9cd0aa63
-- title:
--   BPTCommuting Projector Model: tile subset square same origin of le
-- statement:
--   A core tile is contained in the square envelope with the same lower-left corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2725-L2738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2725-L2738

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
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.tile_subset_square_same_origin_of_le (L : BPTSquareLattice)
    {blockWidth envelopeWidth : Nat} (hwidth : blockWidth ≤ envelopeWidth)
    (index : Nat × Nat) :
    L.tile blockWidth index ⊆
      L.square (index.1 * blockWidth, index.2 * blockWidth) envelopeWidth := by sorry
