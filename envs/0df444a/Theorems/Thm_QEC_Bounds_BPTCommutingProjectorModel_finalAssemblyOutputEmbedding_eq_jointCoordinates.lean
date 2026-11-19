-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyOutputEmbedding_eq_jointCoordinates
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T06:58:22.2392+00:00
-- url     : https://prove2.me/theorems/d09d8eab-e429-47ec-bdb3-5b3012233c16
-- title:
--   BPTCommuting Projector Model: final Assembly Output Embedding eq joint Coordinates
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Output Embedding eq joint Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/JointCoordinates.lean#L34-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/JointCoordinates.lean#L34-L69

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates
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
        (isotypicLiftedMultiplicity.{0} nC))) :
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
      (ccomponent.1.restrictScalars Complex)
    let T := M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC
    let commonCoordinates := composeUnitaryTransport
      (productBlockRegrouping (A := M.fourFactorA region)
        (W := WB.restrictScalars Complex) (N := N) (X := X) (D := D)).symm
      (tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D)
    E = J.comp
      (T.symm.toLinearEquiv.toLinearMap.comp commonCoordinates.toLinearEquiv.toLinearMap) := by sorry
