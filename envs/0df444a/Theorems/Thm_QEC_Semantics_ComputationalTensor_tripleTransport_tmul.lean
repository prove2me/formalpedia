-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalTensor_tripleTransport_tmul
-- name    : QEC.Semantics.ComputationalTensor.tripleTransport_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:22.362145+00:00
-- url     : https://prove2.me/theorems/d59d03aa-0865-47fe-9845-a62288cd25fa
-- title:
--   Computational Tensor: triple Transport tmul
-- statement:
--   Arbitrary pure tensors, not just basis tensors, have the expected product amplitudes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalTensor.lean#L38-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalTensor.lean#L38-L49

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalTensor
open scoped TensorProduct
variable (A B : Type) [Fintype A] [Fintype B]

theorem QEC.Semantics.ComputationalTensor.tripleTransport_tmul (x y z : EuclideanSpace Complex A) (a : A × A × A) :
    tripleTransport A (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z)) a = x a.1 * y a.2.1 * z a.2.2 := by sorry
