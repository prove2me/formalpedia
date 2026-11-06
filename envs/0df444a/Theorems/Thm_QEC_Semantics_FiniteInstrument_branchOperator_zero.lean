-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:28:49.388196+00:00
-- url     : https://prove2.me/theorems/bc59e81e-bdfb-4970-ab95-a40d188a954d
-- title:
--   Finite Instrument: branch Operator zero
-- statement:
--   An observed branch sends the zero unnormalized input operator to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L30-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L30-L34

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

theorem QEC.Semantics.FiniteInstrument.branchOperator_zero (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) :
    I.branchOperator outcome 0 = 0 := by sorry
