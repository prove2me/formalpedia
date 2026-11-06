-- Prove2me | Theorems.Thm_QEC_Semantics_positiveSupportProjection_mul_negativePart
-- name    : QEC.Semantics.positiveSupportProjection_mul_negativePart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:33.572502+00:00
-- url     : https://prove2.me/theorems/0a176157-191d-4bdf-80c2-44fc0ac0858a
-- title:
--   Semantics: positive Support Projection mul negative Part
-- statement:
--   The Semantics construction uses the positive Support Projection mul negative Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L311-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L311-L318

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

theorem QEC.Semantics.positiveSupportProjection_mul_negativePart (A : Operator H) :
    positiveSupportProjection A * (LinearMap.toContinuousLinearMap A)⁻ = 0 := by sorry
