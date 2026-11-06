-- Prove2me | Theorems.Thm_QEC_Semantics_supportProjection_mul_positivePart
-- name    : QEC.Semantics.supportProjection_mul_positivePart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:15.650948+00:00
-- url     : https://prove2.me/theorems/139f8e98-4177-48dd-b9be-c1ffd4f550b6
-- title:
--   Semantics: support Projection mul positive Part
-- statement:
--   The Semantics construction uses the support Projection mul positive Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L299-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L299-L303

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

theorem QEC.Semantics.supportProjection_mul_positivePart (A : Operator H) :
    positiveSupportProjection A * (LinearMap.toContinuousLinearMap A)⁺ =
      (LinearMap.toContinuousLinearMap A)⁺ := by sorry
