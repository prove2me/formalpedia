-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeComplementEmbedding_adjoint_comp_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbedding_adjoint_comp_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:15:14.166473+00:00
-- url     : https://prove2.me/theorems/05f95da1-a6c2-406e-b289-d02712527558
-- title:
--   BPTCommuting Projector Model: active Complement Embedding adjoint comp self
-- statement:
--   The canonical active complement map is a left inverse to its adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L691-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L691-L710

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
set_option maxHeartbeats 200000

theorem QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbedding_adjoint_comp_self
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    let E := M.activeComplementEmbedding region ccomponent WC UC
    (LinearMap.adjoint E.toLinearMap).comp E.toLinearMap =
      (1 : Semantics.Operator
        (ActiveComplementDomain M region nC WC)) := by sorry
