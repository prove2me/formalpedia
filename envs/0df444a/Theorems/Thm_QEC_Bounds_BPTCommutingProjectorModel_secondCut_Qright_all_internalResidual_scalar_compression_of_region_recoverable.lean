-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Qright_all_internalResidual_scalar_compression_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_all_internalResidual_scalar_compression_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T15:08:22.388165+00:00
-- url     : https://prove2.me/theorems/1280ca05-e213-435c-a137-5825b3a55d3a
-- title:
--   BPTCommuting Projector Model: second Cut Qright all internal Residual scalar compression of region recoverable
-- statement:
--   After the hM rank-one `Pi_AB'` reduction, correctability of `M` descends to
--   scalar compression by every operator on the second-cut multiplicity factor
--   `B''`.  The proof transports a literal `B''` probe through the active sector,
--   uses the physical hM relation, and cancels the normalized `Pi_AB'` factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/InternalResidual.lean#L65-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/InternalResidual.lean#L65-L159

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOneTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_all_internalResidual_scalar_compression_of_region_recoverable
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
      ∀ X : Semantics.Operator N, ∃ scalar : Complex,
        Qright * TensorProduct.map X (1 : Semantics.Operator CD) * Qright =
          scalar • Qright := by sorry
