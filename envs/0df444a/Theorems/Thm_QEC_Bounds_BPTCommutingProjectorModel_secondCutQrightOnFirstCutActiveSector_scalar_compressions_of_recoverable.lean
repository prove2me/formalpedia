-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutQrightOnFirstCutActiveSector_scalar_compressions_of_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutQrightOnFirstCutActiveSector_scalar_compressions_of_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T07:24:25.015233+00:00
-- url     : https://prove2.me/theorems/badecaa1-4fa6-44ab-a3eb-d4103819bb67
-- title:
--   BPTCommuting Projector Model: second Cut Qright On First Cut Active Sector scalar compressions of recoverable
-- statement:
--   The two source no-information paths are available on the actual active
--   `B'' tensor C' tensor (C''D)` block.  The first-cut BV03 data, including the
--   arbitrary source complement factor `P_D`, is accepted unchanged; no common
--   factor, residual `Theta`, or scalar conclusion is supplied by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Aggregate.lean#L31-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Aggregate.lean#L31-L86

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_External
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutQrightOnFirstCutActiveSector_scalar_compressions_of_recoverable
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
    M.ActualActiveSectorScalarCompressions region ccomponent WC UC Qsecond := by sorry
