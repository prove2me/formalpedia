-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_comp_adjoint_eq_sectorProjectorProduct
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_comp_adjoint_eq_sectorProjectorProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:00.876484+00:00
-- url     : https://prove2.me/theorems/70935886-ec05-481f-b39f-5726225d8ec2
-- title:
--   BPTCommuting Projector Model: joint BCSector Embedding Right comp adjoint eq sector Projector Product
-- statement:
--   The simultaneous `B,C` sector embedding in `(AB)(CD)` coordinates followed
--   by its adjoint is exactly the product of the two sector projectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L126-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L126-L145

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

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_comp_adjoint_eq_sectorProjectorProduct
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (jointBCSectorEmbeddingRight pB pC).comp
      (LinearMap.adjoint (jointBCSectorEmbeddingRight pB pC)) =
      TensorProduct.map
        (TensorProduct.map (1 : Semantics.Operator A) pB.starProjection.toLinearMap)
        (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D)) := by sorry
