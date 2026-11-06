-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliI_adjoint
-- name    : QEC.Semantics.Qubit.pauliI_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:02:47.890374+00:00
-- url     : https://prove2.me/theorems/027ffd7e-854f-4aa8-9990-e22dbe142488
-- title:
--   Qubit: pauli I adjoint
-- statement:
--   The Qubit construction uses the pauli I adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L225-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L225-L226

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

theorem QEC.Semantics.Qubit.pauliI_adjoint : LinearMap.adjoint pauliI = pauliI := by sorry
