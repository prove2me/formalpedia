-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:28:55.567638+00:00
-- url     : https://prove2.me/theorems/1b3f2eeb-8777-4634-9635-0c397cdab8f1
-- title:
--   BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp overlap Lift Left comp tensor Triple Subtype Embedding
-- statement:
--   Compressing the left member of an overlap pair to an isotypic sector is exactly
--   the previously defined left sector block, with the exterior factor untouched.
--   This is the first concrete factor in the active-block product equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L396-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L396-L424

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        ((overlapLiftLeft (C := C) P).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))) =
      overlapLiftLeft (C := C)
        (overlapProjectorOnIsotypicComponent P component) := by sorry
