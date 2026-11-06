-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:24:38.351436+00:00
-- url     : https://prove2.me/theorems/138eb10f-0384-43ae-b9f7-b633e168b3b9
-- title:
--   BPTCommuting Projector Model: joint BCSector Embedding Right apply tmul
-- statement:
--   The BPTCommuting Projector Model construction uses the joint BCSector Embedding Right apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L110-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L110-L120

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (a : A) (b : pB) (c : pC) (d : D) :
    jointBCSectorEmbeddingRight pB pC ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) =
      (a ⊗ₜ[Complex] b.1) ⊗ₜ[Complex] (c.1 ⊗ₜ[Complex] d) := by sorry

attribute [defeq] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
