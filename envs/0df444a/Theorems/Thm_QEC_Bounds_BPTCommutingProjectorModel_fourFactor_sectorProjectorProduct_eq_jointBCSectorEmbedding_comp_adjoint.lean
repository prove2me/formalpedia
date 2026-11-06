-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:41.922421+00:00
-- url     : https://prove2.me/theorems/a37fc0f8-2aae-484c-94b9-56f7de3219f1
-- title:
--   BPTCommuting Projector Model: four Factor sector Projector Product eq joint BCSector Embedding comp adjoint
-- statement:
--   The product of the two literal four-factor sector lifts is the simultaneous
--   active-sector projection `J J†`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L255-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L255-L272

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map pB.starProjection.toLinearMap
        (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))) *
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map (1 : Semantics.Operator B)
          (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))) =
      (fourFactorJointBCSectorEmbedding pB pC).comp
        (LinearMap.adjoint (fourFactorJointBCSectorEmbedding pB pC)) := by sorry
