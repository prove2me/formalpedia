-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_active_compression_ne_zero_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_active_compression_ne_zero_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:36:15.115539+00:00
-- url     : https://prove2.me/theorems/5cde0a3d-14fa-4ebb-ac38-b938a5c32add
-- title:
--   BPTCommuting Projector Model: first Cut Code Lift active compression ne zero of nonzero code
-- statement:
--   A nonzero active first-cut sector has nonzero literal code compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeNonzero.lean#L53-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeNonzero.lean#L53-L86

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_active_compression_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (hactive : M.firstCutCodeLift region * M.firstCutSectorLift region component =
      M.firstCutCodeLift region) :
    let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let D := M.fourFactorD region
    let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
    ((LinearMap.adjoint J).comp ((M.firstCutCodeLift region).comp J)) ≠ 0 := by sorry
