-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyReassociatedEmbedding_intertwines_exteriorLocal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_intertwines_exteriorLocal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:15:03.762274+00:00
-- url     : https://prove2.me/theorems/f16a8576-ed19-4e32-be16-708a644176ae
-- title:
--   BPTCommuting Projector Model: final Assembly Reassociated Embedding intertwines exterior Local
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Reassociated Embedding intertwines exterior Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RightIntertwining.lean#L26-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RightIntertwining.lean#L26-L83

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Isometry
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RightIntertwining
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

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_intertwines_exteriorLocal
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
    (B : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let O := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    let rightLocal : Semantics.Operator D := TensorProduct.map
      (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
      (M.exteriorCompressionWitness region B)
    (F.conjOperator ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B)).comp
        Enew = Enew.comp
          (TensorProduct.map
            (1 : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem S N) X))
            rightLocal) := by sorry
