-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
-- name    : QEC.Semantics.traceNorm_mul_left_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:16.528553+00:00
-- url     : https://prove2.me/theorems/9ebd5d9a-de08-4000-9fbb-f9b9cb1506a0
-- title:
--   Semantics: trace Norm mul left le
-- statement:
--   The Semantics construction uses the trace Norm mul left le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L125-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L125-L143

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

theorem QEC.Semantics.traceNorm_mul_left_le (A B : Operator H) :
    traceNorm (A * B) ≤ operatorNorm A * traceNorm B := by sorry
