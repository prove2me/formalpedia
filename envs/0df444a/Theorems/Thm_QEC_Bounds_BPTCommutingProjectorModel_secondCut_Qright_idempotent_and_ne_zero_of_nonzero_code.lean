-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:39:32.888488+00:00
-- url     : https://prove2.me/theorems/7c4e872e-b672-4933-8d83-839e6828387b
-- title:
--   BPTCommuting Projector Model: second Cut Qright idempotent and ne zero of nonzero code
-- statement:
--   The second-cut block equality makes the residual right factor nonzero and
--   idempotent.  Both conclusions are derived from the physical code projector,
--   not stored as factorization data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/RightPhysical.lean#L29-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/RightPhysical.lean#L29-L72

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RightPhysical
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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
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
      Qright * Qright = Qright ∧ Qright ≠ 0 := by sorry
