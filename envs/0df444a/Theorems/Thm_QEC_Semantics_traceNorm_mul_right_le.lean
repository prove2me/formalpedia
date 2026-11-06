-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_mul_right_le
-- name    : QEC.Semantics.traceNorm_mul_right_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:17.791193+00:00
-- url     : https://prove2.me/theorems/08886200-2c5d-44e3-811c-c34e110e7f10
-- title:
--   Semantics: trace Norm mul right le
-- statement:
--   The Semantics construction uses the trace Norm mul right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L145-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L145-L170

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

theorem QEC.Semantics.traceNorm_mul_right_le (A B : Operator H) :
    traceNorm (A * B) ≤ operatorNorm B * traceNorm A := by sorry
