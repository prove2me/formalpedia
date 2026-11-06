-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_projectedTail_eq_re_trace
-- name    : QEC.Semantics.traceNorm_projectedTail_eq_re_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:17:30.115143+00:00
-- url     : https://prove2.me/theorems/7a748662-0fc9-41f9-a33c-a937c44b9a04
-- title:
--   Semantics: trace Norm projected Tail eq re trace
-- statement:
--   The Semantics construction uses the trace Norm projected Tail eq re trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L476-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L476-L482

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

theorem QEC.Semantics.traceNorm_projectedTail_eq_re_trace [Nontrivial H]
    (P A : Operator H) (hP : IsStarProjection P) (hA : LinearMap.IsPositive A) :
    traceNorm (projectedTail P A) =
      Complex.re (LinearMap.trace Complex H ((1 - P) * A)) := by sorry
