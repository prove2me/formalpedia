-- Prove2me | Theorems.Thm_QEC_Semantics_projectedTail_trace
-- name    : QEC.Semantics.projectedTail_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:33.099042+00:00
-- url     : https://prove2.me/theorems/5978af0f-dd73-41ef-8f43-a231353d7fe9
-- title:
--   Semantics: projected Tail trace
-- statement:
--   The Semantics construction uses the projected Tail trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L453-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L453-L458

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

theorem QEC.Semantics.projectedTail_trace (P A : Operator H) (hP : IsStarProjection P) :
    LinearMap.trace Complex H (projectedTail P A) =
      LinearMap.trace Complex H ((1 - P) * A) := by sorry
