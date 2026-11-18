-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_lift_of_norm_map
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_lift_of_norm_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:17:51.961527+00:00
-- url     : https://prove2.me/theorems/e9161a44-6210-4a61-b821-776b9cc9289a
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection lift of norm map
-- statement:
--   A norm-preserving linear lift preserves symmetric projections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L423-L430
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L423-L430

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_lift_of_norm_map
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (hnorm : ∀ x, ‖J x‖ = ‖x‖)
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) :
    (J.comp (P.comp (LinearMap.adjoint J))).IsSymmetricProjection := by sorry
