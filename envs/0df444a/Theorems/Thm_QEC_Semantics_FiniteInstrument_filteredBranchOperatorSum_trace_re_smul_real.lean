-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchOperatorSum_trace_re_smul_real
-- name    : QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_trace_re_smul_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:01:26.283286+00:00
-- url     : https://prove2.me/theorems/8e76f0df-3d89-4037-ac75-3626b5bdfaab
-- title:
--   Finite Instrument: filtered Branch Operator Sum trace re smul real
-- statement:
--   Scaling a density operator by a real mass scales the real trace of every
--   filtered branch event by that same mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L94-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L94-L107

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

theorem QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_trace_re_smul_real
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (mass : Real) (rho : DensityOperator K) :
    Complex.re (LinearMap.trace Complex L
      (filteredBranchOperatorSum J predicate
        ((mass : Complex) • rho.toOperator))) =
      mass * ∑ outcome ∈ Finset.univ.filter predicate,
        J.bornWeight outcome rho := by sorry
