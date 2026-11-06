-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
-- name    : QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:08:21.471198+00:00
-- url     : https://prove2.me/theorems/6650b00a-ae75-4ea8-8568-d7a21508b056
-- title:
--   Finite Subsystem: selected Partial Trace to Linear Map
-- statement:
--   The Finite Subsystem construction uses the selected Partial Trace to Linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L301-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L301-L304

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap (S : FiniteSubsystem ι) :
    S.selectedPartialTrace.toLinearMap =
      partialTraceRightRaw S.selectedSystem S.complementSystem := by sorry

attribute [defeq] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
