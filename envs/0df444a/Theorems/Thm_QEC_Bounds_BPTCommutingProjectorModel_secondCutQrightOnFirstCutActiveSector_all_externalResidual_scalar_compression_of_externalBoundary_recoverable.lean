-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutQrightOnFirstCutActiveSector_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutQrightOnFirstCutActiveSector_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T06:56:30.543011+00:00
-- url     : https://prove2.me/theorems/c2e9e9cf-b695-45e7-9754-427e98970ce7
-- title:
--   BPTCommuting Projector Model: second Cut Qright On First Cut Active Sector all external Residual scalar compression of external Boundary recoverable
-- statement:
--   Assemble the pointwise external-residual theorem into the exact probe family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/External.lean#L28-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/External.lean#L28-L92

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Internal
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalAssembly
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_External
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutQrightOnFirstCutActiveSector_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hBleft :
      (unitaryLTensor (M.fourFactorA region) UB).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) Pleft)
    (hBright :
      (unitaryRTensor UB
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qsecond) :
    M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond := by sorry
