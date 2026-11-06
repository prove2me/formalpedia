-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:45.134987+00:00
-- url     : https://prove2.me/theorems/865fd0fb-68b3-4b9c-901f-663c29af324c
-- title:
--   Finite Instrument: tensor Power Selected Partial Trace Channel branch Product matrix Entry eq sum prod
-- statement:
--   The same selected matrix entry, with every recursive branch entry exposed
--   as its actual finite product over trial indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L59-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L59-L100

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod
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
        inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) 0 PUnit.unit)
            (unit
              (tensorPowerBasis
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) 0 PUnit.unit)) *
          ∏ trial : Fin attempts,
            inner Complex
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
                (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
                  ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts
                    observedHistory required hrequired ι).symm (left, complement))
                  trial))
              (branch (tensorPowerHistoryAt α attempts observedHistory trial)
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
                  (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
                    ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts
                      observedHistory required hrequired ι).symm (right, complement))
                    trial))) := by sorry
