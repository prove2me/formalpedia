-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSector_reconstruction_of_active_support
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSector_reconstruction_of_active_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:27:01.825231+00:00
-- url     : https://prove2.me/theorems/5e1980d2-2be0-48a8-8984-f30a39c163cc
-- title:
--   BPTCommuting Projector Model: four Factor Joint BCSector reconstruction of active support
-- statement:
--   A symmetric projection supported on the literal simultaneous `B,C` sector is
--   reconstructed from its compression to that same sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L278-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L278-L331

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSector_reconstruction_of_active_support
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (P4 : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))))
    (hP4 : P4.IsSymmetricProjection)
    (hactive :
      P4 *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map pB.starProjection.toLinearMap
              (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))) *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (1 : Semantics.Operator B)
              (TensorProduct.map pC.starProjection.toLinearMap
                (1 : Semantics.Operator D))) = P4) :
    let J := fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC
    P4 = J.comp (((LinearMap.adjoint J).comp (P4.comp J)).comp (LinearMap.adjoint J)) := by sorry
