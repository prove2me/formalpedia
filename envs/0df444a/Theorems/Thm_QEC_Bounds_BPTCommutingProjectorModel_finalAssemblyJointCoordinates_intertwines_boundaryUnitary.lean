-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyJointCoordinates_intertwines_boundaryUnitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyJointCoordinates_intertwines_boundaryUnitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:18:54.488175+00:00
-- url     : https://prove2.me/theorems/1777b558-3ea7-4969-ae8f-552644f94e1a
-- title:
--   BPTCommuting Projector Model: final Assembly Joint Coordinates intertwines boundary Unitary
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Joint Coordinates intertwines boundary Unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/IntertwiningCore.lean#L29-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/IntertwiningCore.lean#L29-L125

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyJointCoordinates_intertwines_boundaryUnitary
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
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
    let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
    let C := composeUnitaryTransport
      (productBlockRegrouping (A := M.fourFactorA region)
        (W := WB.restrictScalars Complex) (N := N) (X := X) (D := D)).symm
      (tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D)
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Wactive := jointBCSectorActiveUnitary (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
      (activeSectorJointBCUnitary pB pC UB UC U)
    let Vcommon := unitaryLTensor S (unitaryRTensor U D)
    let Vraw := conjugateUnitaryTransport C Vcommon
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let leftExtended := unitaryRTensor leftUnitary D
    let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
    V4.toLinearEquiv.toLinearMap.comp
        (J.comp (T.symm.toLinearEquiv.toLinearMap.comp
          (C.toLinearEquiv.toLinearMap.comp O.toLinearEquiv.toLinearMap))) =
      (J.comp (T.symm.toLinearEquiv.toLinearMap.comp
        (C.toLinearEquiv.toLinearMap.comp O.toLinearEquiv.toLinearMap))).comp
          leftExtended.toLinearEquiv.toLinearMap := by sorry
