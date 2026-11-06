-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorCoordinateOperator_succ
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorCoordinateOperator_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:01:46.010443+00:00
-- url     : https://prove2.me/theorems/62c796bb-a1b2-462d-834e-9feadf412c21
-- title:
--   Finite Instrument: nested Tensor Coordinate Operator succ
-- statement:
--   Selecting a successor-depth nested leaf is the preceding nested
--   coordinate followed by the newest tensor coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L38-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L38-L47

import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
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
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.nestedTensorCoordinateOperator_succ
    (L : Type u) [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (branches depth : Nat)
    (path : nestedTensorPath branches depth) (port : Fin branches)
    (A : Operator (nestedTensorCarrier L branches (depth + 1))) :
    nestedTensorCoordinateOperator L branches (depth + 1) (path, port) A =
      tensorPowerCoordinateOperator branches port
        (nestedTensorCoordinateOperator
          (tensorPowerCarrier L branches) branches depth path A) := by sorry
