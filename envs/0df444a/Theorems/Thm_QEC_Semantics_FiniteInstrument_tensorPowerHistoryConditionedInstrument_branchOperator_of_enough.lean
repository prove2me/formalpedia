-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:33.735584+00:00
-- url     : https://prove2.me/theorems/4966d7ed-7dc2-427d-8ba6-10c3aaf14d8f
-- title:
--   Finite Instrument: tensor Power History Conditioned Instrument branch Operator of enough
-- statement:
--   On an enough-accepted visible history, the total instrument branch uses
--   the literal selected-subsystem channel and never the shortage replacement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedBranchOperator.lean#L52-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedBranchOperator.lean#L52-L70

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (A : Operator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩ A =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required
        hrequired ι ((I.tensorPower attempts).branchOperator history A) := by sorry
