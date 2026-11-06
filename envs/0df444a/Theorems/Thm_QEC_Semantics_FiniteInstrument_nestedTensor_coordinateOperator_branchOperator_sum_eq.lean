-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensor_coordinateOperator_branchOperator_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.nestedTensor_coordinateOperator_branchOperator_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:11.212102+00:00
-- url     : https://prove2.me/theorems/9a2a30f0-5d64-4daa-8849-6f9b8a038a2c
-- title:
--   Finite Instrument: nested Tensor coordinate Operator branch Operator sum eq
-- statement:
--   Retaining a nested leaf of an observed nested tensor branch is exactly
--   the base branch applied to the true unnormalized input-leaf operator after
--   all off-path histories have been summed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBranchOperator.lean#L48-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBranchOperator.lean#L48-L185

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
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

theorem QEC.Semantics.FiniteInstrument.nestedTensor_coordinateOperator_branchOperator_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (branches : Nat) :
    ∀ (depth : Nat) (A : Operator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth) (outcome : Omega),
      nestedTensorCoordinateOperator K branches depth path
          (∑ history : nestedTensorHistory Omega branches depth,
            if nestedTensorHistoryAt Omega branches depth history path = outcome then
              (nestedTensorPower I branches depth).branchOperator history A
            else 0) =
        I.branchOperator outcome
          (nestedTensorCoordinateOperator H branches depth path A) := by sorry
