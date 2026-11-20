-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_card_le_sixteen_mul_interactionRange
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_card_le_sixteen_mul_interactionRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:36.530267+00:00
-- url     : https://prove2.me/theorems/9d51ccdc-6075-4c3c-901e-d158740723a7
-- title:
--   BPTCommuting Projector Model: boundary card le sixteen mul interaction Range
-- statement:
--   The source-thickness coupled-projector boundary has a finite linear bound
--   `|boundary(M)| <= 16 w R`; the proof composes actual-support coverage with the
--   open-boundary strip count, not an assumed entropy or recovery estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1722-L1733
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1722-L1733

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_card_le_sixteen_mul_interactionRange (M : BPTCommutingProjectorModel L kappa)
    (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    (M.boundary (L.lattice.square origin width)).card ≤
      16 * M.interactionRange * width := by sorry
