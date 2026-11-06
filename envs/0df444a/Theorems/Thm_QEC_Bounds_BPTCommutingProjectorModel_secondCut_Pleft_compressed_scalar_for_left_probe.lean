-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_compressed_scalar_for_left_probe
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_compressed_scalar_for_left_probe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:44:08.326243+00:00
-- url     : https://prove2.me/theorems/72122b88-97e9-40a5-afba-245a08e7c03f
-- title:
--   BPTCommuting Projector Model: second Cut Pleft compressed scalar for left probe
-- statement:
--   Compress the physical hM no-information equation to the selected second-cut
--   sector for an arbitrary left-factor probe.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftProbe.lean#L28-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftProbe.lean#L28-L65

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 300000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_compressed_scalar_for_left_probe
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (H W0 : Submodule Complex (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (J : Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) →ₗ[Complex]
      Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
    (hJ : J = tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) H)
    (Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)))
    (U : Semantics.UnitaryTransport H
      (Semantics.CompositeSystem W0 (isotypicLiftedMultiplicity.{0} n)))
    (X : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) W0)) :
    ∃ scalar : Complex,
      Rcompressed *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
            ((unitaryLTensor (M.fourFactorA region) U).symm.conjOperator
              (rightTensorExtensionAfterLeft (M.fourFactorA region) W0
                (isotypicLiftedMultiplicity.{0} n) X)) *
          Rcompressed =
        scalar • Rcompressed := by sorry
