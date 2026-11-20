-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyOutputEmbedding_compression_regionLocal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_compression_regionLocal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:46:44.898053+00:00
-- url     : https://prove2.me/theorems/7b5d1dcd-1284-41cb-a07a-6be10682d9a0
-- title:
--   BPTCommuting Projector Model: final Assembly Output Embedding compression region Local
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Output Embedding compression region Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RegionCompressionRaw.lean#L28-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RegionCompressionRaw.lean#L28-L88

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SelectedTensorCompression
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_compression_regionLocal
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
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    (LinearMap.adjoint E).comp
        ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp E) =
      TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D)) := by sorry
