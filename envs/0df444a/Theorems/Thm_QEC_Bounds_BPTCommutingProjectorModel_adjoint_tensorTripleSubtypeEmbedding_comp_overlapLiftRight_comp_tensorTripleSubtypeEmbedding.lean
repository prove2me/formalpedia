-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:29:15.477365+00:00
-- url     : https://prove2.me/theorems/5a309500-3758-4eff-8365-09d41a34011f
-- title:
--   BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp overlap Lift Right comp tensor Triple Subtype Embedding
-- statement:
--   Compressing the right member of an overlap pair to the same isotypic sector is
--   the literal right sector block.  The associator naturality above is used here
--   to retain the full `B tensor C` action of the right projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L459-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L459-L516

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        ((overlapLiftRight (A := A) Q).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))) =
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component) := by sorry
