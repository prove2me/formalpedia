-- Prove2me | Theorems.Thm_QEC_Semantics_traceNorm_smul
-- name    : QEC.Semantics.traceNorm_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:13.712573+00:00
-- url     : https://prove2.me/theorems/3398b25a-bfba-4540-bb06-2fe78a9599e0
-- title:
--   Semantics: trace Norm smul
-- statement:
--   The Semantics construction uses the trace Norm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L72-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L72-L88

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

theorem QEC.Semantics.traceNorm_smul (c : Complex) (A : Operator H) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by sorry
