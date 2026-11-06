-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedChannel_shortage_iff_no_full_selection
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_shortage_iff_no_full_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:34:40.696924+00:00
-- url     : https://prove2.me/theorems/e8971367-d59d-46a2-bb26-46310649951b
-- title:
--   Finite Instrument: tensor Power History Conditioned Channel shortage iff no full selection
-- statement:
--   The finite shortage predicate is exactly the absence of a full injective
--   selection of accepted trials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L161-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L161-L168

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_shortage_iff_no_full_selection
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat) :
    (tensorPowerAcceptedIndices accepts attempts history).card < required ↔
      ¬ ∃ selection : Fin required → Fin attempts,
        Function.Injective selection ∧
          ∀ slot, selection slot ∈ tensorPowerAcceptedIndices accepts attempts history := by sorry
