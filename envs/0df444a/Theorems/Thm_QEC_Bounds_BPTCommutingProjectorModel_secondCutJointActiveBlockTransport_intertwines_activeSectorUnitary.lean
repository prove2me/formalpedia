-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutJointActiveBlockTransport_intertwines_activeSectorUnitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutJointActiveBlockTransport_intertwines_activeSectorUnitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:13:30.182205+00:00
-- url     : https://prove2.me/theorems/f1c67bb2-99c8-4913-b457-a897cf2eb9b1
-- title:
--   BPTCommuting Projector Model: second Cut Joint Active Block Transport intertwines active Sector Unitary
-- statement:
--   BPT-specialized form of the active second-cut coordinate intertwining identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L69-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L69-L108

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
set_option maxHeartbeats 1600000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCutJointActiveBlockTransport_intertwines_activeSectorUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))) :
    let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
    let Wactive := jointBCSectorActiveUnitary (A := M.fourFactorA region)
      (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
      (ccomponent.1.restrictScalars Complex)
      (activeSectorJointBCUnitary
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex) UB UC U)
    let Vcommon := unitaryLTensor
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)))
    T.conjOperator Wactive.toLinearEquiv.toLinearMap =
      Vcommon.toLinearEquiv.toLinearMap := by sorry
