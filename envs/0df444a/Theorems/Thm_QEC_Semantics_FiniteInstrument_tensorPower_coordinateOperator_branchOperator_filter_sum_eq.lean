-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_coordinateOperator_branchOperator_filter_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_coordinateOperator_branchOperator_filter_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:47.260683+00:00
-- url     : https://prove2.me/theorems/da16cd05-fd0c-41f7-9230-f9d0e35bebbb
-- title:
--   Finite Instrument: tensor Power coordinate Operator branch Operator filter sum eq
-- statement:
--   Summing all global histories selected by a predicate on one coordinate,
--   then tracing to that output coordinate, is the corresponding sum of local
--   observed branches on the true input-coordinate operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FilteredMarginalBranchOperator.lean#L33-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FilteredMarginalBranchOperator.lean#L33-L94

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FilteredMarginalBranchOperator
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

theorem QEC.Semantics.FiniteInstrument.tensorPower_coordinateOperator_branchOperator_filter_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (attempts : Nat) (A : Operator (tensorPowerCarrier H attempts))
    (trial : Fin attempts) :
    tensorPowerCoordinateOperator attempts trial
        (∑ history : tensorPowerHistory Omega attempts,
          if predicate (tensorPowerHistoryAt Omega attempts history trial) then
            (I.tensorPower attempts).branchOperator history A
          else 0) =
      ∑ outcome : Omega,
        if predicate outcome then
          I.branchOperator outcome
            (tensorPowerCoordinateOperator attempts trial A)
        else 0 := by sorry
