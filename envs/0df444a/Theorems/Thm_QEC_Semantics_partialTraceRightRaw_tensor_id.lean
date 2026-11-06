-- Prove2me | Theorems.Thm_QEC_Semantics_partialTraceRightRaw_tensor_id
-- name    : QEC.Semantics.partialTraceRightRaw_tensor_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:48.779285+00:00
-- url     : https://prove2.me/theorems/accdf732-3d8e-40ee-ada5-78b15c024cff
-- title:
--   Semantics: partial Trace Right Raw tensor id
-- statement:
--   Tracing out the right factor of a local operator tensored with the identity
--   multiplies it by the dimension of that factor.
--
--   This is the finite-dimensional normalization law used by coordinate-subsystem
--   interfaces.  It follows from the concrete orthonormal-basis compression
--   construction of `partialTraceRightRaw`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L454-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L454-L472

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder

theorem QEC.Semantics.partialTraceRightRaw_tensor_id (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) :
    (partialTraceRightRaw H K)
        (TensorProduct.map A (LinearMap.id : K →ₗ[Complex] K)) =
      (Module.finrank Complex K : Complex) • A := by sorry
