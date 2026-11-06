-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_actual_joint_active_block_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_actual_joint_active_block_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T17:11:14.048677+00:00
-- url     : https://prove2.me/theorems/ede74392-1561-4740-8a17-23d4866444be
-- title:
--   BPTCommuting Projector Model: second Cut actual joint active block of region recoverable
-- statement:
--   The same physical B-first active block, now expressed through the simultaneous
--   joint `B,C` embedding.  It is obtained by rewriting the sequential block, so
--   the returned `phi` is the very same witness used by the common factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutJoint.lean#L37-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutJoint.lean#L37-L92

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutActive
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutEquality
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutJointData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutJoint
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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_actual_joint_active_block_of_region_recoverable
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
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) )
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) UB).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (WB.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nB) Pleft)
    (hright :
      (unitaryRTensor UB
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qsecond) :
    SecondCutActualJointActiveBlock M region bcomponent ccomponent WB WC UB UC Qsecond := by sorry
