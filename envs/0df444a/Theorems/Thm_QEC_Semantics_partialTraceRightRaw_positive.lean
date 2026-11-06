-- Prove2me | Theorems.Thm_QEC_Semantics_partialTraceRightRaw_positive
-- name    : QEC.Semantics.partialTraceRightRaw_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:12.874774+00:00
-- url     : https://prove2.me/theorems/aab1ed9e-216b-465b-81d9-4915c1bbbf81
-- title:
--   Semantics: partial Trace Right Raw positive
-- statement:
--   The raw right partial trace maps positive composite-system operators to
--   positive operators on the remaining tensor factor.
--
--   This is proved by evaluating `partialTraceRightRaw` as a finite sum of
--   orthonormal-basis compressions and applying positivity of adjoint conjugation.
--   It does not use the `PartialTraceRight` contract fields.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L482-L499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L482-L499

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder

theorem QEC.Semantics.partialTraceRightRaw_positive (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {A : Operator (CompositeSystem H K)}
    (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive ((partialTraceRightRaw H K) A) := by sorry
