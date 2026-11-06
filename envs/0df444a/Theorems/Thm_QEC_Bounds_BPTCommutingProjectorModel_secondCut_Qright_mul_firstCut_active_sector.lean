-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Qright_mul_firstCut_active_sector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_mul_firstCut_active_sector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:52:02.751569+00:00
-- url     : https://prove2.me/theorems/5c9d1995-f06b-4856-9151-8be885752405
-- title:
--   BPTCommuting Projector Model: second Cut Qright mul first Cut active sector
-- statement:
--   The first-cut active `C` sector acts as the identity on the actual second-cut
--   right block.  This is obtained by reassociating the physical first-cut active
--   equation, compressing it through the active `B` sector, and cancelling the
--   nonzero `Pleft` factor; no support property of `Qright` is postulated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L238-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L238-L394

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
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_mul_firstCut_active_sector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) bcomponent) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft)
    (hright :
      (unitaryRTensor U
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
            bcomponent) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} n)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright) :
    Qright * TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} n))
        (TensorProduct.map
          (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
          (1 : Semantics.Operator (M.fourFactorD region))) = Qright := by sorry
