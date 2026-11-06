-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Qright_ne_zero_of_nonzero_code_active_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_ne_zero_of_nonzero_code_active_block
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:51:17.257633+00:00
-- url     : https://prove2.me/theorems/17c93bf8-8b4a-4739-92b8-609fa5464f20
-- title:
--   BPTCommuting Projector Model: second Cut Qright ne zero of nonzero code active block
-- statement:
--   The actual second-cut right block is nonzero on the active `B` sector whenever
--   the physical code is nonempty.  This keeps the later `C`-sector compression
--   honest: nonzeroness is obtained from the active code block, not from the
--   common factorization equality alone.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L154-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L154-L229

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
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
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_ne_zero_of_nonzero_code_active_block
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft)
    (hright :
      (unitaryRTensor U
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} n)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright) :
    Qright ≠ 0 := by sorry
