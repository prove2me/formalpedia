-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_eq_sequential_of_eq_comp
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_eq_sequential_of_eq_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:45:57.867752+00:00
-- url     : https://prove2.me/theorems/7bc7790f-5a10-4b9b-a518-8017882832a9
-- title:
--   BPTCommuting Projector Model: compression eq sequential of eq comp
-- statement:
--   Transport the sequential-compression identity along a concrete embedding factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L38-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L38-L49

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

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_eq_sequential_of_eq_comp
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (J : C →ₗ[Complex] A) (E : B →ₗ[Complex] A) (K : C →ₗ[Complex] B)
    (R : Semantics.Operator A) (hJ : J = E.comp K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp
        (((LinearMap.adjoint E).comp (R.comp E)).comp K) := by sorry
