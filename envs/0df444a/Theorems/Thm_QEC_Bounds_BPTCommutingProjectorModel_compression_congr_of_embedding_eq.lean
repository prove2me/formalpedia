-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_congr_of_embedding_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_congr_of_embedding_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:44:44.839372+00:00
-- url     : https://prove2.me/theorems/bd4942ec-6bbb-4a66-9a09-23385cbdc10b
-- title:
--   BPTCommuting Projector Model: compression congr of embedding eq
-- statement:
--   Compression respects equality of the underlying embeddings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L52-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L52-L59

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

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_congr_of_embedding_eq
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (R : Semantics.Operator A) {J K : B →ₗ[Complex] A} (hJ : J = K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp (R.comp K) := by sorry
