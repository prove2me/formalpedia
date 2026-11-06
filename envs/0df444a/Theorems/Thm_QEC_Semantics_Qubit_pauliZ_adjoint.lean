-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliZ_adjoint
-- name    : QEC.Semantics.Qubit.pauliZ_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:04:56.497575+00:00
-- url     : https://prove2.me/theorems/411d90bf-e262-4d30-9563-ebafed5590bf
-- title:
--   Qubit: pauli Z adjoint
-- statement:
--   The Qubit construction uses the pauli Z adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L240-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L240-L244

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

theorem QEC.Semantics.Qubit.pauliZ_adjoint : LinearMap.adjoint pauliZ = pauliZ := by sorry
