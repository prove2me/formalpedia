-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorCompressionRight_eq_sequentialSecondCutCompression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:44:56.576162+00:00
-- url     : https://prove2.me/theorems/700c7ffd-73af-44e1-8d86-fab7f0ad3ce3
-- title:
--   BPTCommuting Projector Model: joint BCSector Compression Right eq sequential Second Cut Compression
-- statement:
--   Compressing `secondCutCodeLift` through the simultaneous active `B,C`
--   embedding is exactly its sequential `B`-then-`C` compression.  This names the
--   middle block shared by the fixed-witness D5 chain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L217-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L217-L239

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

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    M.secondCutJointCompression region pB pC =
      M.sequentialSecondCutJointCompression region pB pC := by sorry
