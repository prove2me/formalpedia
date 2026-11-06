-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_sum_bornWeight_eq_one
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:35:17.212693+00:00
-- url     : https://prove2.me/theorems/d2624eba-7a5f-4336-bc56-dfdb4dc09a91
-- title:
--   Finite Instrument: tensor Power History Conditioned Instrument sum born Weight eq one
-- statement:
--   The complete total instrument has normalized observable Born mass for
--   every density input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L254-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L254-L270

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_sum_bornWeight_eq_one
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (hI : I.kraus.Complete)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    ∑ outcome,
      (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).bornWeight
        outcome rho = 1 := by sorry
