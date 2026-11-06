-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSectorEmbedding_apply_factor_through_middle
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_apply_factor_through_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:33.402529+00:00
-- url     : https://prove2.me/theorems/c3309f72-915e-4c67-80f6-fc7c614b4a0f
-- title:
--   BPTCommuting Projector Model: four Factor Joint BCSector Embedding apply factor through middle
-- statement:
--   Pointwise form of the preceding joint-embedding factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L287-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L287-L301

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_apply_factor_through_middle
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (x : Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
      (Semantics.CompositeSystem pC D)) :
    fourFactorJointBCSectorEmbedding pB pC x =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
        (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC x)) := by sorry
