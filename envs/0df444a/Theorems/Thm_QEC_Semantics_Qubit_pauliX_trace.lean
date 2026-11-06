-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliX_trace
-- name    : QEC.Semantics.Qubit.pauliX_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:17:48.195036+00:00
-- url     : https://prove2.me/theorems/114491f8-b9f0-4bb5-82d0-80564a7d5393
-- title:
--   Qubit: pauli X trace
-- statement:
--   The Qubit construction uses the pauli X trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L285-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L285-L291

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u

theorem QEC.Semantics.Qubit.pauliX_trace : LinearMap.trace Complex QubitSpace pauliX = 0 := by sorry
