-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssembly_leftCompression_after_boundaryUnitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssembly_leftCompression_after_boundaryUnitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:03:12.282085+00:00
-- url     : https://prove2.me/theorems/ee1c1978-fe79-4c23-a7cc-d5550a118511
-- title:
--   BPTCommuting Projector Model: final Assembly left Compression after boundary Unitary
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly left Compression after boundary Unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/LeftCompression.lean#L32-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/LeftCompression.lean#L32-L137

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompression
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_LeftCompression
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
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssembly_leftCompression_after_boundaryUnitary
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
        (WC.restrictScalars Complex)))
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    let leftLocal : Semantics.Operator
        (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X) :=
      leftUnitary.conjOperator (TensorProduct.map A0 (1 : Semantics.Operator X))
    (LinearMap.adjoint Enew).comp
        ((F.conjOperator
          (Uglobal.conjOperator ((M.regionSubsystem region).extendLocalToRegister A))).comp Enew) =
      TensorProduct.map leftLocal (1 : Semantics.Operator D) := by sorry
