-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:28:22.958056+00:00
-- url     : https://prove2.me/theorems/6c9c7ded-a184-41d1-9411-507b69a6f82f
-- title:
--   BPTCommuting Projector Model: tensor Associator Unitary comp joint BCSector Embedding Left
-- statement:
--   The physical first/second-cut associator intertwines the two simultaneous
--   sector embeddings.  This makes the joint compressed code block a concrete
--   operator independent of whether it is reached from the first or second cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L28-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L28-L68

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D).toLinearEquiv.toLinearMap.comp
        (jointBCSectorEmbeddingLeft pB pC) =
      (jointBCSectorEmbeddingRight pB pC).comp
        (tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D).toLinearEquiv.toLinearMap := by sorry
