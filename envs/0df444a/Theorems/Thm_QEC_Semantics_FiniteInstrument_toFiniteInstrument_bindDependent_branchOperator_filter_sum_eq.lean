-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:36:44.643205+00:00
-- url     : https://prove2.me/theorems/352032bd-c04f-4236-9481-c5cacfd19a2e
-- title:
--   Finite Instrument: to Finite Instrument bind Dependent branch Operator filter sum eq
-- statement:
--   A finite predicate-filtered branch sum after a channel-first dependent
--   bind is the corresponding branch sum of the second instrument on the channel
--   output operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/ChannelFirstFilteredBranchOperator.lean#L33-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/ChannelFirstFilteredBranchOperator.lean#L33-L51

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
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
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq
    (Phi : QuantumChannel H K) (J : FiniteInstrument kappa Omega K L)
    (predicate : Omega -> Prop) [DecidablePred predicate] (A : Operator H) :
    (∑ outcome : Sigma fun _ : PUnit => Omega,
      if predicate outcome.2 then
        (Phi.toFiniteInstrument.bindDependent (fun _ => J)).branchOperator
          outcome A
      else 0) =
      ∑ outcome : Omega,
        if predicate outcome then J.branchOperator outcome (Phi A) else 0 := by sorry
