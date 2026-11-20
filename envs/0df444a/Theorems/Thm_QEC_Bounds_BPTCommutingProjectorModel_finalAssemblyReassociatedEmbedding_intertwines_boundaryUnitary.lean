-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyReassociatedEmbedding_intertwines_boundaryUnitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_intertwines_boundaryUnitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:19:27.038657+00:00
-- url     : https://prove2.me/theorems/c3366fd3-dfd3-4252-8833-46c1b41ab2c3
-- title:
--   BPTCommuting Projector Model: final Assembly Reassociated Embedding intertwines boundary Unitary
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Reassociated Embedding intertwines boundary Unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Intertwining.lean#L31-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Intertwining.lean#L31-L84

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Intertwining
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
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_intertwines_boundaryUnitary
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
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let outerAssociator := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp outerAssociator.toLinearEquiv.toLinearMap
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let leftUnitaryExtended := unitaryRTensor leftUnitary D
    let V4 := fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) (activeSectorPhysicalUnitary pB pC UB UC U)
    V4.toLinearEquiv.toLinearMap.comp Enew =
      Enew.comp leftUnitaryExtended.toLinearEquiv.toLinearMap := by sorry
