-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_sum
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:08:45.946191+00:00
-- url     : https://prove2.me/theorems/a5594b83-ba7b-4753-a242-77dadafb4305
-- title:
--   Finite Instrument: branch Operator sum
-- statement:
--   An observed branch commutes with every finite input-operator sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L64-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L64-L74

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
set_option autoImplicit false
universe u v w x
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.branchOperator_sum (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) {alpha : Type x} [Fintype alpha]
    (A : alpha -> Operator H) :
    I.branchOperator outcome (∑ index, A index) =
      ∑ index, I.branchOperator outcome (A index) := by sorry
