-- Prove2me | Theorems.Thm_QEC_Semantics_norm_trace_le_traceNorm
-- name    : QEC.Semantics.norm_trace_le_traceNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:21.207607+00:00
-- url     : https://prove2.me/theorems/31792677-6485-4324-afe4-03daa4856df1
-- title:
--   Semantics: norm trace le trace Norm
-- statement:
--   The Semantics construction uses the norm trace le trace Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L194-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L194-L197

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

theorem QEC.Semantics.norm_trace_le_traceNorm [Nontrivial H] (A : Operator H) :
    ‖LinearMap.trace Complex H A‖ ≤ traceNorm A := by sorry
