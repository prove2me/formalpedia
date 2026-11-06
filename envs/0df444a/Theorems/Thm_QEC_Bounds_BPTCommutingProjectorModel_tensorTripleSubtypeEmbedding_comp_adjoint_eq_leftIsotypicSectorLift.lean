-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:18:35.079356+00:00
-- url     : https://prove2.me/theorems/7cecf810-4894-43ed-acc1-ef2f2a019929
-- title:
--   BPTCommuting Projector Model: tensor Triple Subtype Embedding comp adjoint eq left Isotypic Sector Lift
-- statement:
--   For an isotypic component, the embedding followed by its adjoint is precisely
--   the physical lift of the local BV03 sector projector.  This connects the
--   subtype coordinate used by the block theorem to the sector selected by the
--   correctability argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L141-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L141-L157

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex)).comp
        (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
          (component.1.restrictScalars Complex))) =
      overlapLiftLeft (C := C)
        (TensorProduct.map (1 : Semantics.Operator A)
          (leftIsotypicSectorProjector P component)) := by sorry
