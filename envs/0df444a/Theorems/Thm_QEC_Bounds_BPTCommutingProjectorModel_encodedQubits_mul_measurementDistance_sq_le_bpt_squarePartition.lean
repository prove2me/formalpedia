-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_mul_measurementDistance_sq_le_bpt_squarePartition
-- name    : QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_mul_measurementDistance_sq_le_bpt_squarePartition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:27:12.457395+00:00
-- url     : https://prove2.me/theorems/6de41673-2dfb-45dc-829f-cd362ad4c5c9
-- title:
--   BPTCommuting Projector Model: encoded Qubits mul measurement Distance sq le bpt square Partition
-- statement:
--   The finite BPT square-partition bound for the source's regular open square
--   lattice.  The visible regularity equality is exactly the source convention;
--   all scale, color, entropy, and finite-remainder facts are constructed here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L3095-L3248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L3095-L3248

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

theorem QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_mul_measurementDistance_sq_le_bpt_squarePartition
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hregular : L.lattice.rows = L.lattice.columns) :
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
      (16384 : Real) * (M.interactionRange : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by sorry
