-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSectorCompression_eq_secondCutCompression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorCompression_eq_secondCutCompression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:19:16.478198+00:00
-- url     : https://prove2.me/theorems/6cb84ae7-1fe3-44f3-af7a-7564b05e930d
-- title:
--   BPTCommuting Projector Model: four Factor Joint BCSector Compression eq second Cut Compression
-- statement:
--   The canonical four-factor joint block is the literal second-cut joint compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L623-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L623-L665

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorCompression_eq_secondCutCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    let J := fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
    let Jright := jointBCSectorEmbeddingRight (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC
    let P4 := (M.fourFactorTransport region).conjOperator M.fullCodeProjector
    (LinearMap.adjoint J).comp (P4.comp J) =
      (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) := by sorry
