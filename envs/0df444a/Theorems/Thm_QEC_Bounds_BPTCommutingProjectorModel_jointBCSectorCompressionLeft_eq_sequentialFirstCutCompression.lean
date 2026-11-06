-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:45:52.576285+00:00
-- url     : https://prove2.me/theorems/fb076ebb-1d51-49aa-9b30-d0bca4ad9279
-- title:
--   BPTCommuting Projector Model: joint BCSector Compression Left eq sequential First Cut Compression
-- statement:
--   Simultaneous first-cut compression agrees with its sequential `C`-then-`B` form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean#L43-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean#L43-L69

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
set_option maxHeartbeats 2000000

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint
      (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.firstCutCodeLift region).comp
        (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      M.sequentialFirstCutJointCompression region pB pC := by sorry
