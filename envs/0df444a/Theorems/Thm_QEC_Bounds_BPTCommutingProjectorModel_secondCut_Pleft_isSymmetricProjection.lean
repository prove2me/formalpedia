-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:37.721865+00:00
-- url     : https://prove2.me/theorems/06e7397d-9abe-4374-897f-b28b1dd07dd5
-- title:
--   BPTCommuting Projector Model: second Cut Pleft is Symmetric Projection
-- statement:
--   The second-cut BV03 left block `Pleft` is an orthogonal projection.  It is
--   obtained by restricting the physical `Pi_AB` projector to the hM-selected
--   sector and reflecting the displayed `Pleft tensor 1` block equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L28-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L28-L59

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      @LinearMap.IsSymmetricProjection Complex
        (Semantics.CompositeSystem A W0) _ _ _ Pleft := by sorry
