-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutFactorizedCompression_eq_sequential
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutFactorizedCompression_eq_sequential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:44:53.342855+00:00
-- url     : https://prove2.me/theorems/565415c6-5913-4a8b-a0da-29b776ea9238
-- title:
--   BPTCommuting Projector Model: second Cut Factorized Compression eq sequential
-- statement:
--   The factorized second-cut embedding realizes the named sequential compression block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L181-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L181-L194

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutFactorizedCompression_eq_sequential
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
      (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
      ((M.secondCutCodeLift region).comp
        ((M.secondCutSelectedBEmbedding region pB).comp
          (M.secondCutSelectedCAfterBEmbedding region pB pC))) =
      M.sequentialSecondCutJointCompression region pB pC := by sorry
