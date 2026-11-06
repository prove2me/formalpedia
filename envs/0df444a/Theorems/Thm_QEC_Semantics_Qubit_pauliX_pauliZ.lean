-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliX_pauliZ
-- name    : QEC.Semantics.Qubit.pauliX_pauliZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:28.289065+00:00
-- url     : https://prove2.me/theorems/970a3697-3dcf-4a0c-ab7e-ee079df01a89
-- title:
--   Qubit: pauli X pauli Z
-- statement:
--   The Qubit construction uses the pauli X pauli Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L272-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L272-L275

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

theorem QEC.Semantics.Qubit.pauliX_pauliZ : pauliX * pauliZ = -Complex.I • pauliY := by sorry
