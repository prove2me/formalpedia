-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Qright_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T15:09:20.026632+00:00
-- url     : https://prove2.me/theorems/76c0a03d-c16a-487e-b50a-cd264dba751c
-- title:
--   BPTCommuting Projector Model: second Cut Qright all external Residual scalar compression of external Boundary recoverable
-- statement:
--   The hC counterpart of the existing hM residual theorem: external-boundary
--   correctability descends to scalar compression by every literal `C` probe on
--   the same second-cut `Qright` block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalResidual.lean#L29-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalResidual.lean#L29-L123

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalResidual
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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_all_externalResidual_scalar_compression_of_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let B := M.fourFactorB region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let C0 := M.fourFactorC region
    let D := M.fourFactorD region
    let CD := Semantics.CompositeSystem C0 D
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
        rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
        leftTensorExtensionBeforeRight W0 N CD Qright →
      M.RegionErasureRecoverable (M.externalBoundary region) →
    ∀ Y : Semantics.Operator C0,
      ∃ scalar : Complex,
        Qright * TensorProduct.map (1 : Semantics.Operator N)
          (TensorProduct.map Y (1 : Semantics.Operator D)) * Qright =
          scalar • Qright := by sorry
