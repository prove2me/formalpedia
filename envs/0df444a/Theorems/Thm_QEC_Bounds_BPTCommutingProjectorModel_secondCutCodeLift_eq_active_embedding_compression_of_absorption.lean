-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_eq_active_embedding_compression_of_absorption
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_eq_active_embedding_compression_of_absorption
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:22:05.409419+00:00
-- url     : https://prove2.me/theorems/ec05710b-a226-4984-a0a0-9e7be2c0268f
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift eq active embedding compression of absorption
-- statement:
--   The selected second-cut sector absorption reconstructs the literal second-cut
--   code lift from its two-sided isotypic-subspace compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L344-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L344-L389

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_eq_active_embedding_compression_of_absorption
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    M.secondCutCodeLift region =
      J.comp (((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)).comp
        (LinearMap.adjoint J)) := by sorry
