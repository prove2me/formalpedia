-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchOperatorSum_smul
-- name    : QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:42.127861+00:00
-- url     : https://prove2.me/theorems/217cfe59-5ebb-4566-adfd-4119fcc50ec5
-- title:
--   Finite Instrument: filtered Branch Operator Sum smul
-- statement:
--   The named filtered branch operator is complex-linear in its
--   unnormalized input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L59-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L59-L73

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

theorem QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_smul
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (c : Complex) (A : Operator K) :
    filteredBranchOperatorSum J predicate (c • A) =
      c • filteredBranchOperatorSum J predicate A := by sorry
