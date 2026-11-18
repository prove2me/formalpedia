-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeComplementProjector_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeComplementProjector_isSymmetricProjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:15:21.611633+00:00
-- url     : https://prove2.me/theorems/9ed23c6d-010a-4d1f-a3d9-b00660be13de
-- title:
--   BPTCommuting Projector Model: active Complement Projector is Symmetric Projection
-- statement:
--   The active complement lift preserves symmetric projections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L732-L757
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L732-L757

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

theorem QEC.Bounds.BPTCommutingProjectorModel.activeComplementProjector_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (ActiveComplementDomain M region nC WC))
    (hP : @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementDomain M region nC WC) _ _ _ P) :
    @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementCodomain M region) _ _ _
      (M.activeComplementProjector region ccomponent WC UC P) := by sorry
