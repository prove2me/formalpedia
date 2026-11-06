-- Prove2me | Theorems.Thm_QEC_Semantics_projectedTail_positive
-- name    : QEC.Semantics.projectedTail_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:47.83922+00:00
-- url     : https://prove2.me/theorems/8371e6ea-238d-4b5e-ba37-6279414120d4
-- title:
--   Semantics: projected Tail positive
-- statement:
--   The Semantics construction uses the projected Tail positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L443-L451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L443-L451

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

theorem QEC.Semantics.projectedTail_positive (P A : Operator H) (hP : IsStarProjection P)
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (projectedTail P A) := by sorry
