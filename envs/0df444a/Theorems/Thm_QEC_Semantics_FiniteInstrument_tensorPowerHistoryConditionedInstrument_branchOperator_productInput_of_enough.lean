-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_branchOperator_productInput_of_enough
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator_productInput_of_enough
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:35.722223+00:00
-- url     : https://prove2.me/theorems/e8647a10-a98c-4687-858d-9af9fb7f65f3
-- title:
--   Finite Instrument: tensor Power History Conditioned Instrument branch Operator product Input of enough
-- statement:
--   On a literal tensorized product input, an enough-history branch is the
--   actual selector applied to the recursively factored observed branch product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedBranchOperator.lean#L74-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedBranchOperator.lean#L74-L97

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator_productInput_of_enough
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (history : tensorPowerHistory Ω attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required
        hrequired ι
        (tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history) := by sorry
