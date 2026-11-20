-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_subset_squareBoundaryFrame
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_subset_squareBoundaryFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:27:16.034221+00:00
-- url     : https://prove2.me/theorems/29c7dd20-d56d-4b6a-b4e6-36e03b0f4f98
-- title:
--   BPTCommuting Projector Model: boundary subset square Boundary Frame
-- statement:
--   Every support participating in the actual boundary of a square lies in the
--   source-thickness frame around that square.  The argument keeps both witnesses
--   to coupling--one site inside and one outside--and uses their common #378
--   support square to rule out the deep interior.  Thus it proves the source's
--   thin-boundary geometry rather than covering the boundary by a whole expanded
--   square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1585-L1631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1585-L1631

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_subset_squareBoundaryFrame
    (M : BPTCommutingProjectorModel L kappa) (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    M.boundary (L.lattice.square origin width) ⊆
      L.lattice.squareBoundaryFrame origin width M.interactionRange := by sorry
