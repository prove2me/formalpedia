-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_actual_commonFactorization_and_jointSecondCutBlock_of_fixed_active_data
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_actual_commonFactorization_and_jointSecondCutBlock_of_fixed_active_data
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T19:54:31.726274+00:00
-- url     : https://prove2.me/theorems/179d7eaa-89fd-436a-b6c7-6a5d1961a419
-- title:
--   BPTCommuting Projector Model: exists actual common Factorization and joint Second Cut Block of fixed active data
-- statement:
--   For fixed BPT sector data, the common-factor equation and the actual
--   simultaneous-sector second-cut block use one and the same normalized `phi`.
--   This is the witness-preserving coordinate-data node for D5; it does not merge
--   independent existential sector choices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/CommonFactorization.lean#L41-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/CommonFactorization.lean#L41-L145

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Blocks
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_CommonFactorizationData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_CommonFactorizationNonzeroData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_CommonFactorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1400000

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_actual_commonFactorization_and_jointSecondCutBlock_of_fixed_active_data
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) )
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
    ActualCommonFactorizationAndJointSecondCutBlock M region bcomponent ccomponent
      WB WC UB UC Pfirst P_D Qsecond := by sorry
