-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_compressed_overlap_block_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressed_overlap_block_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:22:19.113679+00:00
-- url     : https://prove2.me/theorems/d5c7968b-2983-4b74-8340-56196ec25c8a
-- title:
--   BPTCommuting Projector Model: first Cut compressed overlap block product
-- statement:
--   For the physical first BPT cut, compression to an externally-active `C`
--   isotypic sector is exactly the common-unitary tensor block product.  The
--   left-hand side is the literal `Pi_MC Pi_CD` code lift, rather than an
--   abstract overlap pair; this is the point at which the BV03 block calculation
--   enters the source projector proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FirstCutBlock.lean#L31-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FirstCutBlock.lean#L31-L68

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressed_overlap_block_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
      (unitaryRTensor U D).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component) =
          leftTensorExtensionBeforeRight W0 N D Qright →
      (isotypicSectorBlockTransportLeft AB H W0 N D U).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := AB) (C := D) H)).comp
            ((M.firstCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding (A := AB) (C := D) H))) =
        TensorProduct.map Pleft Qright := by sorry
