-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchOperatorSum_eq_sum_filter
-- name    : QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_eq_sum_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:02:37.130274+00:00
-- url     : https://prove2.me/theorems/d51eadda-6b26-4488-8ddc-dfe50bc75fca
-- title:
--   Finite Instrument: filtered Branch Operator Sum eq sum filter
-- statement:
--   A named filtered branch sum is the same finite sum written over the
--   filtered visible-outcome set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/FilteredBranchMeasurement.lean#L37-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/FilteredBranchMeasurement.lean#L37-L46

import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.FiniteInstrument
open Classical
open scoped BigOperators
universe u v w x y
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {mu : Type x} [Fintype mu]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_eq_sum_filter
    (I : FiniteInstrument kappa Omega H K)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (A : Operator H) :
    filteredBranchOperatorSum I predicate A =
      ∑ outcome ∈ Finset.univ.filter predicate,
        I.branchOperator outcome A := by sorry
