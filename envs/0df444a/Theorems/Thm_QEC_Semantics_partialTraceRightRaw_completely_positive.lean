-- Prove2me | Theorems.Thm_QEC_Semantics_partialTraceRightRaw_completely_positive
-- name    : QEC.Semantics.partialTraceRightRaw_completely_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:52.887607+00:00
-- url     : https://prove2.me/theorems/8e42e504-5699-446e-acf7-8f4a76d98b84
-- title:
--   Semantics: partial Trace Right Raw completely positive
-- statement:
--   The raw right partial trace is completely positive.
--
--   The proof works at every finite matrix amplification size. It rewrites
--   `partialTraceRightRaw` as a finite sum of orthonormal-basis compressions, then
--   expresses each block quadratic form as a finite sum of nonnegative pulled-back
--   quadratic forms for the original positive block matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L509-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L509-L585

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder

theorem QEC.Semantics.partialTraceRightRaw_completely_positive (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    CompletelyPositive (partialTraceRightRaw H K) := by sorry
