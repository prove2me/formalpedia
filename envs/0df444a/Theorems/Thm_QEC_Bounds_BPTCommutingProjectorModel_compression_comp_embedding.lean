-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_comp_embedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_comp_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:44:35.684966+00:00
-- url     : https://prove2.me/theorems/429dccb0-5124-4096-8b75-3c90633bdaf3
-- title:
--   BPTCommuting Projector Model: compression comp embedding
-- statement:
--   Compression through a composite embedding is the corresponding sequential compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L25-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L25-L35

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

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_comp_embedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (E : B →ₗ[Complex] A) (K : C →ₗ[Complex] B) (R : Semantics.Operator A) :
    (LinearMap.adjoint (E.comp K)).comp (R.comp (E.comp K)) =
      (LinearMap.adjoint K).comp
        (((LinearMap.adjoint E).comp (R.comp E)).comp K) := by sorry
