-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_apply_tensorAssociatorUnitary_symm_tmul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_apply_tensorAssociatorUnitary_symm_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:29:12.461451+00:00
-- url     : https://prove2.me/theorems/6d602a9f-9482-4406-a2d5-4095979391ef
-- title:
--   BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding apply tensor Associator Unitary symm tmul
-- statement:
--   The adjoint sector embedding commutes with reassociation when the exterior
--   factor is fixed.  This is the concrete naturality needed to compress the
--   right member of an overlap pair even though that operator may produce an
--   arbitrary vector of the physical middle tensor factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L432-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L432-L452

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_apply_tensorAssociatorUnitary_symm_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (interior : A)
    (middle : Semantics.CompositeSystem B C) :
    LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)
      ((tensorAssociatorUnitary A B C).symm (interior ⊗ₜ[Complex] middle)) =
      (tensorAssociatorUnitary A p C).symm
        (interior ⊗ₜ[Complex]
          (TensorProduct.map (LinearMap.adjoint p.subtype)
            (1 : Semantics.Operator C) middle)) := by sorry
