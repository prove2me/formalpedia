-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:31.596991+00:00
-- url     : https://prove2.me/theorems/5ea55e7a-95ac-44f8-ad49-40903b421abf
-- title:
--   Finite Instrument: nested Tensor coordinate Operator branch Operator filter sum eq
-- statement:
--   Filtering a nested global history by one leaf observation, then retaining
--   that output leaf, is the corresponding sum of local observed branches on the
--   true input-leaf operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/FilteredMarginalBranchOperator.lean#L33-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/FilteredMarginalBranchOperator.lean#L33-L96

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (branches depth : Nat) (A : Operator (nestedTensorCarrier H branches depth))
    (path : nestedTensorPath branches depth) :
    nestedTensorCoordinateOperator K branches depth path
        (∑ history : nestedTensorHistory Omega branches depth,
          if predicate
              (nestedTensorHistoryAt Omega branches depth history path) then
            (nestedTensorPower I branches depth).branchOperator history A
          else 0) =
      ∑ outcome : Omega,
        if predicate outcome then
          I.branchOperator outcome
            (nestedTensorCoordinateOperator H branches depth path A)
        else 0 := by sorry
