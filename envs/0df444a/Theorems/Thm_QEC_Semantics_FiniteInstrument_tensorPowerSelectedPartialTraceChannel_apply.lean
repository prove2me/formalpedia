-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:54.274828+00:00
-- url     : https://prove2.me/theorems/7fd57117-1fdc-42c7-bbdb-4706a0346066
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel apply
-- statement:
--   The selected-subsystem channel acts by the stated flatten, partial-trace,
--   and reindex composition on every operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean#L258-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean#L258-L269

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)) :
    tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι A =
      (tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι).conjOperator
        ((tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selectedPartialTraceFromRegister
          ((tensorPowerQubitRegisterTransport ι attempts).conjOperator A)) := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
