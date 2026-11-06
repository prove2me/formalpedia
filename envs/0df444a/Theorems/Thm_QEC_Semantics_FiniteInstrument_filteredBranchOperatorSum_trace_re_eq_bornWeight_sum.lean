-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchOperatorSum_trace_re_eq_bornWeight_sum
-- name    : QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_trace_re_eq_bornWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:35.549065+00:00
-- url     : https://prove2.me/theorems/ee8fe6c8-f7f8-41f8-bdf7-fbc1cdb4ed96
-- title:
--   Finite Instrument: filtered Branch Operator Sum trace re eq born Weight sum
-- statement:
--   On a density input, the real trace of a filtered branch operator is the
--   literal filtered Born-mass sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L77-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L77-L90

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

theorem QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_trace_re_eq_bornWeight_sum
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (rho : DensityOperator K) :
    Complex.re (LinearMap.trace Complex L
      (filteredBranchOperatorSum J predicate rho.toOperator)) =
      ∑ outcome ∈ Finset.univ.filter predicate,
        J.bornWeight outcome rho := by sorry
