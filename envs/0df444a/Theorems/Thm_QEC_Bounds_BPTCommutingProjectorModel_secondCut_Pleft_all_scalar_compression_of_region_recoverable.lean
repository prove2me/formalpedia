-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_all_scalar_compression_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_all_scalar_compression_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:44:35.061568+00:00
-- url     : https://prove2.me/theorems/cba21444-d486-4e09-b33a-877aeb969e6e
-- title:
--   BPTCommuting Projector Model: second Cut Pleft all scalar compression of region recoverable
-- statement:
--   The hM no-information equation descends through the active second BV03
--   sector to scalar compression by every operator on `Pleft`.  The proof uses
--   the physical-region probe, the literal compressed code relation, and the
--   residual tensor-factor cancellation; it is the source's `Pi_AB'` argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftPhysical.lean#L30-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftPhysical.lean#L30-L90

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 12000000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_all_scalar_compression_of_region_recoverable
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
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
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
      ∀ X : Semantics.Operator (Semantics.CompositeSystem A W0),
        ∃ scalar : Complex, Pleft * X * Pleft = scalar • Pleft := by sorry
