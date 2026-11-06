-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_one_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.one_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:01.0821+00:00
-- url     : https://prove2.me/theorems/29ae744e-4765-47df-9244-dde8b3f1ebe0
-- title:
--   BPTCommuting Projector Model: one is Symmetric Projection
-- statement:
--   The identity operator is an orthogonal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3802-L3809
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3802-L3809

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.one_isSymmetricProjection
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] :
    (1 : Semantics.Operator H).IsSymmetricProjection := by sorry
