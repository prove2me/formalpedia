-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_coordinateOperator_branchOperator_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_coordinateOperator_branchOperator_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:24.209323+00:00
-- url     : https://prove2.me/theorems/b179b76d-0454-4824-892a-687e8f0d1c49
-- title:
--   Finite Instrument: tensor Power coordinate Operator branch Operator sum eq
-- statement:
--   For an arbitrary operator on a recursive tensor-power carrier, summing
--   all observed histories off one selected coordinate and physically tracing to
--   that output coordinate gives the local observed branch applied to the true
--   input-coordinate operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean#L227-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean#L227-L329

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.tensorPower_coordinateOperator_branchOperator_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (A : Operator (tensorPowerCarrier H attempts))
      (trial : Fin attempts) (outcome : Omega),
      tensorPowerCoordinateOperator attempts trial
          (∑ history : tensorPowerHistory Omega attempts,
            if tensorPowerHistoryAt Omega attempts history trial = outcome then
              (I.tensorPower attempts).branchOperator history A
            else 0) =
        I.branchOperator outcome
          (tensorPowerCoordinateOperator attempts trial A) := by sorry
