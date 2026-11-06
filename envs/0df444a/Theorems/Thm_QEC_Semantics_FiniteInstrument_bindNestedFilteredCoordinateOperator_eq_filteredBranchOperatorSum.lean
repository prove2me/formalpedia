-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
-- name    : QEC.Semantics.FiniteInstrument.bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:47:14.193653+00:00
-- url     : https://prove2.me/theorems/5ddabacd-ad77-4964-b149-8a9ded627400
-- title:
--   Finite Instrument: bind Nested Filtered Coordinate Operator eq filtered Branch Operator Sum
-- statement:
--   Named-operator form of the sequential selected-coordinate identity.  This
--   keeps downstream concrete protocols from unfolding and comparing the complete
--   dependent history enumeration merely to instantiate the source-neutral law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L253-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean#L253-L268

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

theorem QEC.Semantics.FiniteInstrument.bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) :
    bindNestedFilteredCoordinateOperator branches depth I J
        firstPredicate secondPredicate path A =
      filteredBranchOperatorSum J secondPredicate
        (nestedFilteredPredecessorCoordinateOperator branches depth I
          firstPredicate path A) := by sorry
