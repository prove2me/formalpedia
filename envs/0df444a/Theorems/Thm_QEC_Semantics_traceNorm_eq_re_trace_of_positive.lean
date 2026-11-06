-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_eq_re_trace_of_positive
-- name    : QEC.Semantics.traceNorm_eq_re_trace_of_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:30.78329+00:00
-- url     : https://prove2.me/theorems/311c4aad-57fe-4fb9-8369-2051d21d3a64
-- title:
--   Semantics: trace Norm eq re trace of positive
-- statement:
--   On positive operators, the trace norm specializes to the real trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L200-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L200-L228

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.traceNorm_eq_re_trace_of_positive [Nontrivial H]
    (A : Operator H) (hA : LinearMap.IsPositive A) :
    traceNorm A = Complex.re (LinearMap.trace Complex H A) := by sorry
