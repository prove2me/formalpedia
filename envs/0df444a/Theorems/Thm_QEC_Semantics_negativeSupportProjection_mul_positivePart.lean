-- Prove2me | Theorems.Thm_QEC_Semantics_negativeSupportProjection_mul_positivePart
-- name    : QEC.Semantics.negativeSupportProjection_mul_positivePart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:04.937203+00:00
-- url     : https://prove2.me/theorems/28a8ae33-2a27-469b-956e-c9e4fa818ca8
-- title:
--   Semantics: negative Support Projection mul positive Part
-- statement:
--   The Semantics construction uses the negative Support Projection mul positive Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L320-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L320-L327

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

theorem QEC.Semantics.negativeSupportProjection_mul_positivePart (A : Operator H) :
    negativeSupportProjection A * (LinearMap.toContinuousLinearMap A)⁺ = 0 := by sorry
