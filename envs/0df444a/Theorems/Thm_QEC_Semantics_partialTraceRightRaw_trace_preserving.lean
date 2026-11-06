-- Prove2me | Theorems.Thm_QEC_Semantics_partialTraceRightRaw_trace_preserving
-- name    : QEC.Semantics.partialTraceRightRaw_trace_preserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:57:03.897701+00:00
-- url     : https://prove2.me/theorems/6d1bd5e8-9ad4-40f2-800f-76fa1dd6646c
-- title:
--   Semantics: partial Trace Right Raw trace preserving
-- statement:
--   The raw right partial trace preserves trace.
--
--   This is proved directly from the tensor contraction defining
--   `partialTraceRightRaw`; it does not use the `PartialTraceRight` contract fields.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L380-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L380-L400

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder

theorem QEC.Semantics.partialTraceRightRaw_trace_preserving (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator (CompositeSystem H K)) :
    LinearMap.trace Complex H ((partialTraceRightRaw H K) A) =
      LinearMap.trace Complex (CompositeSystem H K) A := by sorry
