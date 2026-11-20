-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_locallyMaximalCorrectableSquareScale
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_locallyMaximalCorrectableSquareScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:29.728416+00:00
-- url     : https://prove2.me/theorems/8661907e-06e4-4358-b203-86f39213747a
-- title:
--   BPTCommuting Projector Model: exists locally Maximal Correctable Square Scale
-- statement:
--   For a nonzero encoded-qubit parameter, a finite first failure along the exact
--   `2w` source growth progression yields the required locally maximal square
--   scale.  The terminal failure is concrete: an origin-zero square wider than
--   both finite lattice dimensions is the full lattice, whose recovery would
--   force `k = 0` by the #389 entropy theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2217-L2284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2217-L2284

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

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_locallyMaximalCorrectableSquareScale
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (hseed : M.AllSquareBlocksRecoverable (4 * M.interactionRange))
    (hpositive : 0 < parameter.encodedQubits) :
    ∃ width, 4 * M.interactionRange ≤ width ∧
      M.LocallyMaximalCorrectableSquareScale width := by sorry
