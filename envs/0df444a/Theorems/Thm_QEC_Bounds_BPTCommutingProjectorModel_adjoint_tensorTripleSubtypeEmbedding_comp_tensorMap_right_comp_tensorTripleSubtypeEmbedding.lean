-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_tensorMap_right_comp_tensorTripleSubtypeEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_tensorMap_right_comp_tensorTripleSubtypeEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:02:14.182198+00:00
-- url     : https://prove2.me/theorems/e60f3cf2-3e37-4bb9-be80-7846e5a75384
-- title:
--   BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp tensor Map right comp tensor Triple Subtype Embedding
-- statement:
--   Compressing a literal exterior tensor lift through an active isotypic sector
--   leaves the exterior operator intact.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean#L127-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean#L127-L152

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_tensorMap_right_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (Z : Semantics.Operator C) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      ((TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A B)) Z).comp
        (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A p)) Z := by sorry
