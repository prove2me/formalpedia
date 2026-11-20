-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
-- name    : QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:19.835542+00:00
-- url     : https://prove2.me/theorems/02abed80-f86d-435e-b46a-1efd7ff6b9ad
-- title:
--   BPTCommuting Projector Model: encoded Qubits le square Partition C card mul log uniform Dimension
-- statement:
--   The #389 entropy complement is exactly the finite C corner region, so the
--   uniform local-dimension bound gives the source inequality `k <= |C| log_2 D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2591-L2643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2591-L2643

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

theorem QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (blockWidth margin : Nat)
    (hA : M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin))
    (hB : M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin)) :
    (parameter.encodedQubits : Real) ≤
      ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
        Real.logb 2 (L.uniformDimensionBound : Real) := by sorry
