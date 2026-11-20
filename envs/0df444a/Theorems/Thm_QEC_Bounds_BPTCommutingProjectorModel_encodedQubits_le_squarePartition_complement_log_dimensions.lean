-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_le_squarePartition_complement_log_dimensions
-- name    : QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_squarePartition_complement_log_dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:55.985604+00:00
-- url     : https://prove2.me/theorems/ad704bdc-9c09-46a4-bcbf-fdb7d27e5cc8
-- title:
--   BPTCommuting Projector Model: encoded Qubits le square Partition complement log dimensions
-- statement:
--   The #389 entropy theorem specialized to the source-constructed square
--   partition.  The hypotheses are typed erasure-recovery facts for the actual
--   `A` and `B` sets; later partition lemmas must construct them through #370 and
--   #403 rather than replace them by an entropy assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2568-L2585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2568-L2585

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

theorem QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_squarePartition_complement_log_dimensions
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (blockWidth margin : Nat)
    (hA : M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin))
    (hB : M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin)) :
    (parameter.encodedQubits : Real) <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem (L.lattice.squarePartitionA blockWidth margin))
        (M.regionSubsystem (L.lattice.squarePartitionB blockWidth margin))).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by sorry
