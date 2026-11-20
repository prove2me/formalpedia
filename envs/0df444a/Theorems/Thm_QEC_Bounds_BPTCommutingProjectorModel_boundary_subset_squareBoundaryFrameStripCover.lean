-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_subset_squareBoundaryFrameStripCover
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_subset_squareBoundaryFrameStripCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:11.129622+00:00
-- url     : https://prove2.me/theorems/112483a0-9e88-4ca2-82c3-e25555c35102
-- title:
--   BPTCommuting Projector Model: boundary subset square Boundary Frame Strip Cover
-- statement:
--   The actual coupled-projector boundary of a square is covered by the four
--   finite source-thickness strips.  Unlike a naively translated enlarged square,
--   the strips do not shift clipped lower-boundary width to the opposite side of
--   an open lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1639-L1715
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1639-L1715

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_subset_squareBoundaryFrameStripCover
    (M : BPTCommutingProjectorModel L kappa) (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    M.boundary (L.lattice.square origin width) ⊆
      L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange := by sorry
