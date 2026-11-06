-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_maximallyMixedSelected_trace_one
-- name    : QEC.Semantics.QuditSubsystem.maximallyMixedSelected_trace_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:16:03.717365+00:00
-- url     : https://prove2.me/theorems/f5d49ed9-5299-4509-baaa-49393ba8dc75
-- title:
--   Qudit Subsystem: maximally Mixed Selected trace one
-- statement:
--   The Qudit Subsystem construction uses the maximally Mixed Selected trace one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L159-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L159-L161

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.maximallyMixedSelected_trace_one (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    LinearMap.trace Complex S.selectedSystem (S.maximallyMixedSelected hq).toOperator = 1 := by sorry
