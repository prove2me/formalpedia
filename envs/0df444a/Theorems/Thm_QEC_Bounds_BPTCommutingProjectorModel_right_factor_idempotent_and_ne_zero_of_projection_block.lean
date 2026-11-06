-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_idempotent_and_ne_zero_of_projection_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.right_factor_idempotent_and_ne_zero_of_projection_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:37:22.608692+00:00
-- url     : https://prove2.me/theorems/2847989b-3818-4580-a0ba-2fca66b0f30a
-- title:
--   BPTCommuting Projector Model: right factor idempotent and ne zero of projection block
-- statement:
--   An actual nonzero compressed projection block supplies all algebra needed for
--   the right tensor factor: idempotence and nonzeroness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean#L100-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean#L100-L117

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.right_factor_idempotent_and_ne_zero_of_projection_block
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (R : Semantics.Operator S) (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hR : R ≠ 0) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hRprojection : R.IsSymmetricProjection)
    (hblock : T.conjOperator R = TensorProduct.map P Q) :
    Q * Q = Q ∧ Q ≠ 0 := by sorry
