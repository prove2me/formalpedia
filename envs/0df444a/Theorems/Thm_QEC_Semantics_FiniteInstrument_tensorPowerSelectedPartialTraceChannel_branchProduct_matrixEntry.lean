-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:12.81579+00:00
-- url     : https://prove2.me/theorems/73c02e72-8e7e-43fa-8a55-43c199a2989d
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel branch Product matrix Entry
-- statement:
--   A requested matrix entry of a selected tensorized branch is the sum of
--   the exact recursive branch-entry products over one discarded label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L26-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L26-L55

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (branch : α → Operator (Qubit.QubitRegister ι))
    (unit : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          (tensorPowerBranchOperatorProduct branch unit attempts observedHistory)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        tensorPowerBranchOperatorMatrixEntryProduct
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
          branch unit attempts observedHistory
          ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
            required hrequired ι).symm (left, complement))
          ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
            required hrequired ι).symm (right, complement)) := by sorry
