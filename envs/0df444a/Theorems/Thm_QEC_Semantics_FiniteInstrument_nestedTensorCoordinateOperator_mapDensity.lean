-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorCoordinateOperator_mapDensity
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorCoordinateOperator_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:01:28.901028+00:00
-- url     : https://prove2.me/theorems/9d1742f6-3f0b-4e0a-98c4-609b31da1964
-- title:
--   Finite Instrument: nested Tensor Coordinate Operator map Density
-- statement:
--   The operator selected recursively above is the true density marginal when
--   the input operator itself is a density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBranchOperator.lean#L189-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBranchOperator.lean#L189-L214

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

theorem QEC.Semantics.FiniteInstrument.nestedTensorCoordinateOperator_mapDensity
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) :
    ∀ (depth : Nat) (rho : DensityOperator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth),
      (nestedTensorCoordinateOperator H branches depth path).mapDensity rho =
        nestedTensorInputMarginal H branches depth rho path := by sorry
