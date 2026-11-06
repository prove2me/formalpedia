-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
-- name    : QEC.Semantics.FiniteInstrument.bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:57.45012+00:00
-- url     : https://prove2.me/theorems/969814dd-5102-4030-ba5d-5ec6bd11ac1e
-- title:
--   Finite Instrument: bind Nested Filtered Coordinate Operator trace re eq born Weight sum
-- statement:
--   The real trace of one selected sequential nested event is its literal
--   finite Born-mass sum.  Retaining the selected output coordinate does not
--   change the trace because that marginal map is a quantum channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L273-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L273-L303

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

theorem QEC.Semantics.FiniteInstrument.bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (rho : DensityOperator H) :
    Complex.re (LinearMap.trace Complex L
      (bindNestedFilteredCoordinateOperator branches depth I J
        firstPredicate secondPredicate path rho.toOperator)) =
      ∑ outcome : Sigma fun _ : Omega =>
          nestedTensorHistory Xi branches depth,
        if firstPredicate outcome.1 ∧
            secondPredicate
              (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
          (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
            outcome rho
        else 0 := by sorry
