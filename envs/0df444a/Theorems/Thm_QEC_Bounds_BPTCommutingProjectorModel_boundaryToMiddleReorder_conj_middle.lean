-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryToMiddleReorder_conj_middle
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryToMiddleReorder_conj_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:59.348209+00:00
-- url     : https://prove2.me/theorems/2610be99-e2c3-4f63-8276-84e57769e316
-- title:
--   BPTCommuting Projector Model: boundary To Middle Reorder conj middle
-- statement:
--   The boundary-to-middle permutation carries an operator on `BC` to the middle
--   factor while leaving the source interior and exterior identities untouched.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1586-L1607
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1586-L1607

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryToMiddleReorder_conj_middle
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (P : Semantics.Operator (Semantics.CompositeSystem B C)) :
    (boundaryToMiddleReorder A B C D).conjOperator
        (TensorProduct.map P (1 : Semantics.Operator (Semantics.CompositeSystem A D))) =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map P (1 : Semantics.Operator D)) := by sorry
