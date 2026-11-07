-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_of_two_step_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_of_two_step_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:33:05.429898+00:00
-- url     : https://prove2.me/theorems/9d578a75-5b8d-4608-b63b-6579c6b53039
-- title:
--   BPTCommuting Projector Model: unitary RTensor conj of two step factorization
-- statement:
--   Transport a two-step left-factor identification through a right-tensored unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ProductFactorization.lean#L23-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ProductFactorization.lean#L23-L49

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Bounds.BPTCommutingProjectorModel

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_of_two_step_factorization
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem N C) (Semantics.CompositeSystem N C))
    (Q : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem N C) D))
    (Theta A B : Semantics.Operator (Semantics.CompositeSystem N C))
    (P : Semantics.Operator D)
    (hfactor : Q = TensorProduct.map Theta P)
    (hTheta : Theta = A)
    (hconj : U.conjOperator A = B) :
    (unitaryRTensor U D).conjOperator Q = TensorProduct.map B P := by sorry
