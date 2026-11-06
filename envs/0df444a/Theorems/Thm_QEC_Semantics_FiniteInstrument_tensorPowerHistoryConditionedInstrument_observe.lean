-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_observe
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:35:06.449523+00:00
-- url     : https://prove2.me/theorems/f54516d0-db58-4452-9137-637fad199244
-- title:
--   Finite Instrument: tensor Power History Conditioned Instrument observe
-- statement:
--   The total instrument's visible outcome records the actual first-stage
--   observed history and the unit observation of the selected second channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L195-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L195-L222

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_observe
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (firstIndex : tensorPowerHistory κ attempts)
    (secondIndex : Fin
      ((tensorPowerHistoryConditionedChannel accepts attempts
        ((I.tensorPower attempts).observe firstIndex) required ι shortageState).chosenKrausCount)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).observe
      ⟨firstIndex, secondIndex⟩ =
        ⟨(I.tensorPower attempts).observe firstIndex, PUnit.unit⟩ := by sorry
