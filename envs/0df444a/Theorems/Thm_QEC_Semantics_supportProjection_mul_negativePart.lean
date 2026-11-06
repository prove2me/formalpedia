-- Prove2me | Theorems.Thm_QEC_Semantics_supportProjection_mul_negativePart
-- name    : QEC.Semantics.supportProjection_mul_negativePart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:38.500033+00:00
-- url     : https://prove2.me/theorems/3908a2cf-dea3-4deb-8480-8d515c8aba24
-- title:
--   Semantics: support Projection mul negative Part
-- statement:
--   The Semantics construction uses the support Projection mul negative Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L305-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L305-L309

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

theorem QEC.Semantics.supportProjection_mul_negativePart (A : Operator H) :
    negativeSupportProjection A * (LinearMap.toContinuousLinearMap A)⁻ =
      (LinearMap.toContinuousLinearMap A)⁻ := by sorry
