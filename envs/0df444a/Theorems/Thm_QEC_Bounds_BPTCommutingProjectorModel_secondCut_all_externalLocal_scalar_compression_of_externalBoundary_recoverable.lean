-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:01:34.117561+00:00
-- url     : https://prove2.me/theorems/879765e7-685d-4265-85c6-1177ba5aae35
-- title:
--   BPTCommuting Projector Model: second Cut all external Local scalar compression of external Boundary recoverable
-- statement:
--   External-boundary recoverability gives scalar compression by every literal
--   `C` probe in the second-cut coordinates.  This is the physical hC relation
--   needed for the same `Qright` residual that already receives the hM relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean#L29-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean#L29-L123

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (E : Semantics.Operator (M.fourFactorC region)) :
    ∃ scalar : Complex,
      M.secondCutCodeLift region *
          TensorProduct.map
            (1 : Semantics.Operator
              (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)))
            (TensorProduct.map E (1 : Semantics.Operator (M.fourFactorD region))) *
          M.secondCutCodeLift region = scalar • M.secondCutCodeLift region := by sorry
