-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_neg
-- name    : QEC.Semantics.traceNorm_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:05.362039+00:00
-- url     : https://prove2.me/theorems/2c4a2d3d-2651-45c4-9d88-6538b7689c7c
-- title:
--   Semantics: trace Norm neg
-- statement:
--   The Semantics construction uses the trace Norm neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L384-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L384-L385

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

theorem QEC.Semantics.traceNorm_neg (A : Operator H) : traceNorm (-A) = traceNorm A := by sorry
