-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalTensor_tripleMap_basis_apply
-- name    : QEC.Semantics.ComputationalTensor.tripleMap_basis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:45.41785+00:00
-- url     : https://prove2.me/theorems/14b58e7a-ce9a-4a2c-8ffb-e38e457711ba
-- title:
--   Computational Tensor: triple Map basis apply
-- statement:
--   The Computational Tensor construction uses the triple Map basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalTensor.lean#L58-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalTensor.lean#L58-L73

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalTensor
open scoped TensorProduct
variable (A B : Type) [Fintype A] [Fintype B]

theorem QEC.Semantics.ComputationalTensor.tripleMap_basis_apply
    (f : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B)
    (a : A × A × A) (b : B × B × B) :
    tripleMap A B f (EuclideanSpace.basisFun _ Complex a) b =
      f (EuclideanSpace.basisFun _ Complex a.1) b.1 *
        f (EuclideanSpace.basisFun _ Complex a.2.1) b.2.1 *
        f (EuclideanSpace.basisFun _ Complex a.2.2) b.2.2 := by sorry
