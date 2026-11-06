-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_congr
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:15.896193+00:00
-- url     : https://prove2.me/theorems/8ca11452-48bf-445d-ac69-202bf93c588c
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection congr
-- statement:
--   Orthogonal-projection structure transports across an equality of operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3732-L3737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3732-L3737

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_congr
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] {P Q : Semantics.Operator H}
    (hP : P.IsSymmetricProjection) (hPQ : P = Q) : Q.IsSymmetricProjection := by sorry
