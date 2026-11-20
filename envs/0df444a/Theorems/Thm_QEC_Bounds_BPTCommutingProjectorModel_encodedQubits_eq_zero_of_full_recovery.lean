-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_eq_zero_of_full_recovery
-- name    : QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_eq_zero_of_full_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:46.642837+00:00
-- url     : https://prove2.me/theorems/a4ccd611-8983-479f-bc8b-d6270b7f6e0a
-- title:
--   BPTCommuting Projector Model: encoded Qubits eq zero of full recovery
-- statement:
--   Recovering the entire finite lattice forces the source encoded-qubit parameter to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2182-L2208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2182-L2208

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

theorem QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_eq_zero_of_full_recovery
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (hfull : M.RegionErasureRecoverable Finset.univ) :
    parameter.encodedQubits = 0 := by sorry
