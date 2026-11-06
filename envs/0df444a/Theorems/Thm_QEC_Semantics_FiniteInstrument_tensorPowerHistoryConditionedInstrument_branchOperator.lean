-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_branchOperator
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:21.572391+00:00
-- url     : https://prove2.me/theorems/2cd6a456-41f4-4022-b9ad-94101a667423
-- title:
--   Finite Instrument: tensor Power History Conditioned Instrument branch Operator
-- statement:
--   The visible history branch of the total conditioned instrument is the
--   actual tensor-power branch sent through the channel chosen by that history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedBranchOperator.lean#L24-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedBranchOperator.lean#L24-L48

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (A : Operator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩ A =
      tensorPowerHistoryConditionedChannel accepts attempts history required ι
        shortageState ((I.tensorPower attempts).branchOperator history A) := by sorry
