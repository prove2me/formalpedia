-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:42.137056+00:00
-- url     : https://prove2.me/theorems/f0160075-62eb-4c07-815e-447e2201a73f
-- title:
--   BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp tensor Triple Subtype Embedding
-- statement:
--   The finite triple embedding is an isometry.  This is the first half of the
--   active-block reconstruction: the compressed overlap projector can be returned
--   to the physical three-factor space without altering vectors in its sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L79-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L79-L104

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      (tensorTripleSubtypeEmbedding (A := A) (C := C) p) =
        (1 : Semantics.Operator
          (Semantics.CompositeSystem (Semantics.CompositeSystem A p) C)) := by sorry
