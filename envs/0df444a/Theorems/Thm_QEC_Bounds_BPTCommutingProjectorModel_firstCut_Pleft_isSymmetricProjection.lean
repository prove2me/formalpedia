-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_Pleft_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_Pleft_isSymmetricProjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:35:58.518937+00:00
-- url     : https://prove2.me/theorems/33920a00-70a4-4466-93c6-4e0b1bed38e8
-- title:
--   BPTCommuting Projector Model: first Cut Pleft is Symmetric Projection
-- statement:
--   The active first-cut left BV03 block is an orthogonal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutLeftProjection.lean#L24-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutLeftProjection.lean#L24-L55

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_Pleft_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem AB W0)),
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
        @LinearMap.IsSymmetricProjection Complex
          (Semantics.CompositeSystem AB W0) _ _ _ Pleft := by sorry
