-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutFactorizedCompression_eq_sequential
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutFactorizedCompression_eq_sequential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:46:37.965897+00:00
-- url     : https://prove2.me/theorems/e7cb9c52-4cf0-4a0c-b310-9b8961a0a274
-- title:
--   BPTCommuting Projector Model: first Cut Factorized Compression eq sequential
-- statement:
--   The factorized first-cut embedding realizes the named sequential compression block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean#L26-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean#L26-L39

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutFactorizedCompression_eq_sequential
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.firstCutSelectedCEmbedding region pC).comp
      (M.firstCutSelectedBAfterCEmbedding region pB pC))).comp
      ((M.firstCutCodeLift region).comp
        ((M.firstCutSelectedCEmbedding region pC).comp
          (M.firstCutSelectedBAfterCEmbedding region pB pC))) =
      M.sequentialFirstCutJointCompression region pB pC := by sorry
