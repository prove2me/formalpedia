-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_Pleft_ne_zero_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_Pleft_ne_zero_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:38:13.048428+00:00
-- url     : https://prove2.me/theorems/59b77c55-1fec-4d2d-a755-17bdaf17c30c
-- title:
--   BPTCommuting Projector Model: first Cut Pleft ne zero of nonzero code
-- statement:
--   A nonempty active first-cut block has a nonzero left BV03 factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutFactorNonzero.lean#L25-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutFactorNonzero.lean#L25-L71

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutFactorNonzero
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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_Pleft_ne_zero_of_nonzero_code
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
      Pleft ≠ 0 := by sorry
