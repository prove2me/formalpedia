-- Prove2me | Theorems.Thm_QEC_Semantics_tracePairing_smul
-- name    : QEC.Semantics.tracePairing_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:22:26.475331+00:00
-- url     : https://prove2.me/theorems/8ffdc4ba-659e-4289-9595-20c2631ee41a
-- title:
--   Semantics: trace Pairing smul
-- statement:
--   The Semantics construction uses the trace Pairing smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L62-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L62-L65

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

theorem QEC.Semantics.tracePairing_smul (c : Complex) (A : Operator H) :
    tracePairing (c • A) = c • tracePairing A := by sorry
