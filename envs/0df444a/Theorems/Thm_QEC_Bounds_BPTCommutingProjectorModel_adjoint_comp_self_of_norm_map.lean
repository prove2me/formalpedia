-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_comp_self_of_norm_map
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_comp_self_of_norm_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:13:09.366199+00:00
-- url     : https://prove2.me/theorems/d757a944-1276-40aa-8f25-23ec9ef67185
-- title:
--   BPTCommuting Projector Model: adjoint comp self of norm map
-- statement:
--   A norm-preserving linear map is a left inverse to its finite-dimensional adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L403-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L403-L420

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_comp_self_of_norm_map
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (hnorm : ∀ x, ‖J x‖ = ‖x‖) :
    (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H) := by sorry
