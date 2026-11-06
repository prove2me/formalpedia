-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_nestedTensor_bornWeight_first_implies_path_and_any_failure_le_filteredBranchTrace
-- name    : QEC.Semantics.FiniteInstrument.bind_nestedTensor_bornWeight_first_implies_path_and_any_failure_le_filteredBranchTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:02:18.422027+00:00
-- url     : https://prove2.me/theorems/dc7d6c5f-942f-4711-aaa7-e18bda1c63db
-- title:
--   Finite Instrument: bind nested Tensor born Weight first implies path and any failure le filtered Branch Trace
-- statement:
--   Implication-aware form of the same union bound.  A global predecessor
--   event may be stronger than the selected predecessor-path event; it suffices
--   to prove that the global event implies the selected event at every charged
--   path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L426-L543
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L426-L543

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

theorem QEC.Semantics.FiniteInstrument.bind_nestedTensor_bornWeight_first_implies_path_and_any_failure_le_filteredBranchTrace
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (globalPredicate : Omega -> Prop) [DecidablePred globalPredicate]
    (pathPredicate : nestedTensorPath branches depth -> Omega -> Prop)
    [∀ path, DecidablePred (pathPredicate path)]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (hglobal : ∀ outcome path,
      globalPredicate outcome -> pathPredicate path outcome)
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth =>
          globalPredicate outcome.1 ∧
            ∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)),
      (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
        outcome rho) <=
      ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              (pathPredicate path) path rho.toOperator))) := by sorry
