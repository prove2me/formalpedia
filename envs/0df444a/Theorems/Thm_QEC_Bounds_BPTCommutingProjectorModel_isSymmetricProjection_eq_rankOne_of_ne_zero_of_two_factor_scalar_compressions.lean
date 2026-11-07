-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_eq_rankOne_of_ne_zero_of_two_factor_scalar_compressions
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_eq_rankOne_of_ne_zero_of_two_factor_scalar_compressions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:32:41.174483+00:00
-- url     : https://prove2.me/theorems/165a907c-2710-4e3b-9fb1-11b2e10baded
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection eq rank One of ne zero of two factor scalar compressions
-- statement:
--   A nonzero two-factor scalar-compressed projection is rank one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L535-L548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L535-L548

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_eq_rankOne_of_ne_zero_of_two_factor_scalar_compressions
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hleft : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (hright : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P) :
    ∃ phi : Semantics.CompositeSystem N C, ‖phi‖ = 1 ∧
      P = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by sorry
