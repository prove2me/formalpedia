-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSectorEmbedding_factor_through_middle
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_factor_through_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:23.811571+00:00
-- url     : https://prove2.me/theorems/c90d8f19-57f0-4f22-ac6b-6d6b8f8f2283
-- title:
--   BPTCommuting Projector Model: four Factor Joint BCSector Embedding factor through middle
-- statement:
--   The canonical joint active embedding factors through the parenthesization
--   which exposes the physical `B tensor C` middle factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L248-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L248-L284

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_factor_through_middle
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm.toLinearEquiv.toLinearMap.comp
        ((jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC).comp
          (jointBCSectorMiddleTransport (A := A) pB pC).toLinearEquiv.toLinearMap) := by sorry
