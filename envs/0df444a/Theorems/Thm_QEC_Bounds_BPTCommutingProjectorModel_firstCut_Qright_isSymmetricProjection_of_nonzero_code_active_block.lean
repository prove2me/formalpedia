-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_Qright_isSymmetricProjection_of_nonzero_code_active_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_Qright_isSymmetricProjection_of_nonzero_code_active_block
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:41:50.750898+00:00
-- url     : https://prove2.me/theorems/a2e71b21-facc-49da-95b6-06f48838b2f6
-- title:
--   BPTCommuting Projector Model: first Cut Qright is Symmetric Projection of nonzero code active block
-- statement:
--   The source `Pi_C''D` factor is a nonzero orthogonal projection on the active
--   first-cut block.  It is the concrete arbitrary `P_D` retained by the residual
--   no-cloning argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/ResidualProjection.lean#L29-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/ResidualProjection.lean#L29-L92

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_Qright_isSymmetricProjection_of_nonzero_code_active_block
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
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
    let D := M.fourFactorD region
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem AB W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N D)),
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          M.firstCutCodeLift region →
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
      (unitaryRTensor U D).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component) =
          leftTensorExtensionBeforeRight W0 N D Qright →
      Qright.IsSymmetricProjection ∧ Qright ≠ 0 := by sorry
