-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_nestedTensor_bornWeight_first_and_any_path_failure_le_filteredBranchTrace
-- name    : QEC.Semantics.FiniteInstrument.bind_nestedTensor_bornWeight_first_and_any_path_failure_le_filteredBranchTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:01:48.114464+00:00
-- url     : https://prove2.me/theorems/e644e6bc-ebb9-452e-90e5-553eb37569e9
-- title:
--   Finite Instrument: bind nested Tensor born Weight first and any path failure le filtered Branch Trace
-- statement:
--   A source-neutral union bound for a filtered predecessor event followed by
--   a nested stage.  Each possible failing leaf is charged to the real trace of
--   its local filtered branch on the true unnormalized predecessor marginal.
--   No branch is normalized and no product or sibling-independence premise is
--   used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L310-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L310-L420

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

theorem QEC.Semantics.FiniteInstrument.bind_nestedTensor_bornWeight_first_and_any_path_failure_le_filteredBranchTrace
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth =>
          firstPredicate outcome.1 ∧
            ∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)),
      (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
        outcome rho) <=
      ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              firstPredicate path rho.toOperator))) := by sorry
