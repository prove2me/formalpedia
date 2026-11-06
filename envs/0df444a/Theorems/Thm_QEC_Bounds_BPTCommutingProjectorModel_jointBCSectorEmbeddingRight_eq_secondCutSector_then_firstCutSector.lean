-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:44:15.657294+00:00
-- url     : https://prove2.me/theorems/7dce0df2-d547-43b6-82e6-44326e0c7b09
-- title:
--   BPTCommuting Projector Model: joint BCSector Embedding Right eq second Cut Sector then first Cut Sector
-- statement:
--   The simultaneous `B,C` compression in second-cut coordinates is literally the
--   second-cut `B` compression followed by the selected first-cut `C` sector.
--   This is the concrete embedding identity used to compare the two active BV03
--   blocks, rather than an additional factorization assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L152-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L152-L177

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

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    jointBCSectorEmbeddingRight (A := M.fourFactorA region) pB pC =
      (M.secondCutSelectedBEmbedding region pB).comp
        (M.secondCutSelectedCAfterBEmbedding region pB pC) := by sorry
