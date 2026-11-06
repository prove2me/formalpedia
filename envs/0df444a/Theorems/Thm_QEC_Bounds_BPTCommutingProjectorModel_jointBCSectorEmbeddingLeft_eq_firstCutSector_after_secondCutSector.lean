-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:45:04.255237+00:00
-- url     : https://prove2.me/theorems/0cc5b318-2431-40df-b961-5f29b5c46dde
-- title:
--   BPTCommuting Projector Model: joint BCSector Embedding Left eq first Cut Sector after second Cut Sector
-- statement:
--   The simultaneous `B,C` compression in first-cut coordinates is literally the
--   first-cut `C` compression following the selected second-cut `B` sector.  It
--   is the companion concrete coordinate identity for the common active block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L246-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L246-L271

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

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    jointBCSectorEmbeddingLeft (A := M.fourFactorA region) pB pC =
      (M.firstCutSelectedCEmbedding region pC).comp
        (M.firstCutSelectedBAfterCEmbedding region pB pC) := by sorry
