-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_productInputBranch_matrixEntry
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_productInputBranch_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:21.613852+00:00
-- url     : https://prove2.me/theorems/2419fead-a850-401f-a10d-100f42f0df94
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel product Input Branch matrix Entry
-- statement:
--   On a literal tensor-product input, a selected branch matrix entry is the
--   product of the retained local branch entries and the Born weights of every
--   discarded actual trial.  This is a partial-trace identity, not an independence
--   assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L127-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L127-L182

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_productInputBranch_matrixEntry
    {κ Ω : Type v} [Fintype κ] [Fintype Ω]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory Ω attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          ((I.tensorPower attempts).branchOperator observedHistory
            (tensorPowerProductInput rho rhoUnit attempts).toOperator)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            right)) =
      (∏ slot : Fin required,
        inner Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
            (fun port => left (slot, port)))
          (I.branchOperator
            (tensorPowerHistoryAt Ω attempts observedHistory
              (tensorPowerAcceptedSelector accepts attempts observedHistory
                required hrequired slot))
            rho.toOperator
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
              (fun port => right (slot, port))))) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts observedHistory
          required hrequired,
        (I.bornWeight
          (tensorPowerHistoryAt Ω attempts observedHistory trial.1) rho : Complex) := by sorry
