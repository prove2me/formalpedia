-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:38.575784+00:00
-- url     : https://prove2.me/theorems/6ec23328-38c5-4d81-acc9-308a116e2b43
-- title:
--   BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp overlap Lift Left subtype Lift comp
-- statement:
--   Compressing the zero-extended subtype probe through the triple sector
--   embedding recovers the literal subtype probe on the left overlap factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L43-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L43-L93

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (E : Semantics.Operator (Semantics.CompositeSystem A p)) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      ((overlapLiftLeft (C := C) (overlapLeftSubtypeLift p E)).comp
        (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
      overlapLiftLeft (C := C) E := by sorry
