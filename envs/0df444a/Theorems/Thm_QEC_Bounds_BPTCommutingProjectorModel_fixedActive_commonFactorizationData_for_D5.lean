-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fixedActive_commonFactorizationData_for_D5
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fixedActive_commonFactorizationData_for_D5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-17T22:05:29.881605+00:00
-- url     : https://prove2.me/theorems/cff9369f-0286-4bb0-aa92-65127e844c6b
-- title:
--   BPTCommuting Projector Model: fixed Active common Factorization Data for D5
-- statement:
--   The BPTCommuting Projector Model construction uses the fixed Active common Factorization Data for D5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/Common.lean#L31-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/Common.lean#L31-L106

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ResidualData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Common
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.fixedActive_commonFactorizationData_for_D5
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hCleft :
      (unitaryLTensor
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) UC).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) ccomponent) =
        rightTensorExtensionAfterLeft
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (WC.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nC) Pfirst)
    (hCright :
      (unitaryRTensor UC (M.fourFactorD region)).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) ccomponent) =
        leftTensorExtensionBeforeRight (WC.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) P_D)
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
    M.FixedActiveCommonFactorizationData
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond := by sorry
