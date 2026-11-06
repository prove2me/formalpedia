-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliY_adjoint
-- name    : QEC.Semantics.Qubit.pauliY_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:04:13.439815+00:00
-- url     : https://prove2.me/theorems/131e9aef-3cf0-4d7b-b7c5-d1f84ab9252f
-- title:
--   Qubit: pauli Y adjoint
-- statement:
--   The Qubit construction uses the pauli Y adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L234-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L234-L238

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

theorem QEC.Semantics.Qubit.pauliY_adjoint : LinearMap.adjoint pauliY = pauliY := by sorry
