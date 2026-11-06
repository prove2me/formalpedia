-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
-- name    : QEC.Semantics.traceNorm_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:25.139203+00:00
-- url     : https://prove2.me/theorems/599bb133-b43b-408b-95d9-d60144e15702
-- title:
--   Semantics: trace Norm eq zero iff
-- statement:
--   The Semantics construction uses the trace Norm eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L99-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L99-L110

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

theorem QEC.Semantics.traceNorm_eq_zero_iff (A : Operator H) : traceNorm A = 0 ↔ A = 0 := by sorry
