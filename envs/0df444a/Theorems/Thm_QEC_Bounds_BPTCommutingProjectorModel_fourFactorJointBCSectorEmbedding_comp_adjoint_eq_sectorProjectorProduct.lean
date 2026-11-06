-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSectorEmbedding_comp_adjoint_eq_sectorProjectorProduct
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_comp_adjoint_eq_sectorProjectorProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:26.635018+00:00
-- url     : https://prove2.me/theorems/7027fb15-c959-400d-9753-90d55e32d4cc
-- title:
--   BPTCommuting Projector Model: four Factor Joint BCSector Embedding comp adjoint eq sector Projector Product
-- statement:
--   The canonical simultaneous-sector embedding has `J J†` equal to the literal
--   product of the `B` and `C` sector projections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L209-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L209-L249

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_comp_adjoint_eq_sectorProjectorProduct
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (fourFactorJointBCSectorEmbedding pB pC).comp
      (LinearMap.adjoint (fourFactorJointBCSectorEmbedding pB pC)) =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map pB.starProjection.toLinearMap
          (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D))) := by sorry
