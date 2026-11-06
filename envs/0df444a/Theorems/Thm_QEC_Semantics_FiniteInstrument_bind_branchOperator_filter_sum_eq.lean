-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_branchOperator_filter_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.bind_branchOperator_filter_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:36.825503+00:00
-- url     : https://prove2.me/theorems/d945e5c5-19c1-4456-bdd1-4ba6dba286f2
-- title:
--   Finite Instrument: bind branch Operator filter sum eq
-- statement:
--   Filtering both retained observations of a sequential bind may be
--   regrouped by first outcome, with the second-stage branch sum applied to the
--   first-stage unnormalized branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/FilteredBranchOperator.lean#L35-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/FilteredBranchOperator.lean#L35-L67

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
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

theorem QEC.Semantics.FiniteInstrument.bind_branchOperator_filter_sum_eq
    (I : FiniteInstrument kappa Omega H K)
    (J : Omega -> FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Omega -> Xi -> Prop)
    [∀ firstOutcome, DecidablePred (secondPredicate firstOutcome)]
    (A : Operator H) :
    (∑ outcome : Sigma fun _ : Omega => Xi,
      if firstPredicate outcome.1 ∧
          secondPredicate outcome.1 outcome.2 then
        (I.bind (fun firstOutcome => J firstOutcome)).branchOperator outcome A
      else 0) =
      ∑ firstOutcome : Omega,
        if firstPredicate firstOutcome then
          ∑ secondOutcome : Xi,
            if secondPredicate firstOutcome secondOutcome then
              (J firstOutcome).branchOperator secondOutcome
                (I.branchOperator firstOutcome A)
            else 0
        else 0 := by sorry
