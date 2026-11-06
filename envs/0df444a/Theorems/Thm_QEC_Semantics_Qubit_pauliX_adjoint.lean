-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliX_adjoint
-- name    : QEC.Semantics.Qubit.pauliX_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:03:04.669645+00:00
-- url     : https://prove2.me/theorems/873880f0-de40-41a3-a7de-7f2d0782e7b0
-- title:
--   Qubit: pauli X adjoint
-- statement:
--   The Qubit construction uses the pauli X adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L228-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L228-L232

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

theorem QEC.Semantics.Qubit.pauliX_adjoint : LinearMap.adjoint pauliX = pauliX := by sorry
