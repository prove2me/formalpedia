-- Prove2me | Theorems.Thm_QEC_Semantics_parts_range_isOrtho
-- name    : QEC.Semantics.parts_range_isOrtho
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:38.159577+00:00
-- url     : https://prove2.me/theorems/444508bf-6347-4431-b3cb-c9818578b76f
-- title:
--   Semantics: parts range is Ortho
-- statement:
--   The Semantics construction uses the parts range is Ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L274-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L274-L292

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

theorem QEC.Semantics.parts_range_isOrtho (A : Operator H) :
    ((LinearMap.toContinuousLinearMap A)⁺).range ⟂
      ((LinearMap.toContinuousLinearMap A)⁻).range := by sorry
