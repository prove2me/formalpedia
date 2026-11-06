-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliZ_trace
-- name    : QEC.Semantics.Qubit.pauliZ_pauliZ_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:41:45.214209+00:00
-- url     : https://prove2.me/theorems/4578261d-cb5d-448d-9617-4efe4f9e8a65
-- title:
--   Qubit: pauli Z pauli Z trace
-- statement:
--   The Qubit construction uses the pauli Z pauli Z trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L351-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L351-L355

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

theorem QEC.Semantics.Qubit.pauliZ_pauliZ_trace :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliZ) = (2 : Complex) := by sorry
