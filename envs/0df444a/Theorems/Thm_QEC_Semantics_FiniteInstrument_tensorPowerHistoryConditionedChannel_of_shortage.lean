-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedChannel_of_shortage
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_of_shortage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:34:55.976313+00:00
-- url     : https://prove2.me/theorems/7772a87e-e7bf-4759-9007-c07b2959b76e
-- title:
--   Finite Instrument: tensor Power History Conditioned Channel of shortage
-- statement:
--   A shortage history reduces to the physical replacement channel, rather
--   than being interpreted as an accepted selected subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L147-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L147-L157

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_of_shortage
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat)
    (hshort : (tensorPowerAcceptedIndices accepts attempts history).card < required)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState =
      fixedDensityReplacementChannel
        (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
        (Qubit.QubitRegister (Fin required × ι)) shortageState := by sorry
