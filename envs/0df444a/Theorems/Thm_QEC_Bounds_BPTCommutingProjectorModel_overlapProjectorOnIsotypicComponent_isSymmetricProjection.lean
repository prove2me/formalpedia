-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlapProjectorOnIsotypicComponent_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlapProjectorOnIsotypicComponent_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:27:01.407217+00:00
-- url     : https://prove2.me/theorems/efa968fb-f8c5-45f9-988e-7c2c8ce0156d
-- title:
--   BPTCommuting Projector Model: overlap Projector On Isotypic Component is Symmetric Projection
-- statement:
--   The left projector restricted to an isotypic sector remains an orthogonal
--   projection.  Its invariance is obtained from the actual interaction algebra,
--   so the resulting statement applies directly to the second-cut `Pleft` block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Projection.lean#L92-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Projection.lean#L92-L138

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.overlapProjectorOnIsotypicComponent_isSymmetricProjection
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (hP : P.IsSymmetricProjection)
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (overlapProjectorOnIsotypicComponent P component).IsSymmetricProjection := by sorry
