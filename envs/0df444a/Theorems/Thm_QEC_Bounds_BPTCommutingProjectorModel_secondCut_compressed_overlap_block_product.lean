-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressed_overlap_block_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_block_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:23:46.760403+00:00
-- url     : https://prove2.me/theorems/df7c0271-0dde-4ded-bffa-eee52d24fd87
-- title:
--   BPTCommuting Projector Model: second Cut compressed overlap block product
-- statement:
--   For the physical second BPT cut, compression to an hM-selected internal
--   boundary sector is exactly the common-unitary tensor block product.  This is
--   the literal `Pi_AB Pi_Bbar(M)` source lift, so its `Pleft` factor is the
--   `AB'` projector which the region no-information argument must make rank one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Compression.lean#L30-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Compression.lean#L30-L68

import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Compression
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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_block_product
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
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      (isotypicSectorBlockTransportLeft A H W0 N CD U).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := CD) H)).comp
            ((M.secondCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding (A := A) (C := CD) H))) =
        TensorProduct.map Pleft Qright := by sorry
