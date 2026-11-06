-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_associator_coherence
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_associator_coherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:42.871199+00:00
-- url     : https://prove2.me/theorems/6299354d-4843-442e-856a-e6365b49a07d
-- title:
--   BPTCommuting Projector Model: first Cut associator coherence
-- statement:
--   The associator coherence used by the `BC` support calculation.  This is the
--   finite-dimensional tensor identity which moves an arbitrary `BC` vector from
--   the first-cut parenthesization into the common four-factor parenthesization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2765-L2782
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2765-L2782

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_associator_coherence
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (x : Semantics.CompositeSystem B C) (d : D) :
    (TensorProduct.assoc Complex A B (Semantics.CompositeSystem C D))
        ((TensorProduct.assoc Complex (Semantics.CompositeSystem A B) C D)
          ((TensorProduct.assoc Complex A B C).symm (a ⊗ₜ[Complex] x) ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex]
        (TensorProduct.assoc Complex B C D (x ⊗ₜ[Complex] d)) := by sorry
