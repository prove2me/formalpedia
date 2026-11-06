-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedChannel_of_enough
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_of_enough
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:12.280886+00:00
-- url     : https://prove2.me/theorems/ea2ace13-bb23-4272-bb55-f8fd25aa3f57
-- title:
--   Finite Instrument: tensor Power History Conditioned Channel of enough
-- statement:
--   An enough-accepted history reduces definitionally to its literal selected
--   subsystem partial-trace channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L135-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L135-L143

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_of_enough
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι := by sorry
