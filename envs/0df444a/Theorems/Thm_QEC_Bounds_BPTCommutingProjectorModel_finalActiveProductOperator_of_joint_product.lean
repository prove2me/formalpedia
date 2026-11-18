-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalActiveProductOperator_of_joint_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalActiveProductOperator_of_joint_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:18:28.619024+00:00
-- url     : https://prove2.me/theorems/c11cb02c-5b65-40d1-8226-d12e7e43bda6
-- title:
--   BPTCommuting Projector Model: final Active Product Operator of joint product
-- statement:
--   The two fixed active transports assemble the final common-coordinate product operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L555-L619
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L555-L619

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
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

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalActiveProductOperator_of_joint_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Qprime : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))))
    (Z : Semantics.Operator (FinalActiveProductDomain M region nB nC WB WC))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (hjoint : Z =
        (unitaryLTensor
          (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
          (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm).conjOperator
          (rankOneTensorOperator phi Qprime))
    (hproduct :
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).conjOperator
          ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm.conjOperator Qprime) =
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap P_D) :
    let Vcommon := unitaryLTensor
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)))
    Vcommon.conjOperator Z =
      M.finalActiveProductOperator region WB WC phi n0 c0 P_D := by sorry
