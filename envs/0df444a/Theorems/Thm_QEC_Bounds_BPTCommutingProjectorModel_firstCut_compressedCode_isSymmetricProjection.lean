-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_compressedCode_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressedCode_isSymmetricProjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:39:30.143025+00:00
-- url     : https://prove2.me/theorems/ad9606c4-9221-4a0b-9232-57fca8a2e79e
-- title:
--   BPTCommuting Projector Model: first Cut compressed Code is Symmetric Projection
-- statement:
--   The active first-cut code compressed to its selected `C` sector is a projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeProjection.lean#L25-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeProjection.lean#L25-L71

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutFactorNonzero
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeProjection
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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressedCode_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let D := M.fourFactorD region
    let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
    ((LinearMap.adjoint J).comp ((M.firstCutCodeLift region).comp J)).IsSymmetricProjection := by sorry
