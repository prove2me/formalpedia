-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_add
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:01.605025+00:00
-- url     : https://prove2.me/theorems/83fc1723-3760-4006-a1c7-a31862f788ad
-- title:
--   Finite Instrument: branch Operator add
-- statement:
--   An observed branch preserves addition of unnormalized input operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L37-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L37-L47

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

theorem QEC.Semantics.FiniteInstrument.branchOperator_add (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) (A B : Operator H) :
    I.branchOperator outcome (A + B) =
      I.branchOperator outcome A + I.branchOperator outcome B := by sorry
