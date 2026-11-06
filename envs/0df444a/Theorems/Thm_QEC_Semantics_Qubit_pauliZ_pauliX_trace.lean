-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliX_trace
-- name    : QEC.Semantics.Qubit.pauliZ_pauliX_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:41:39.415311+00:00
-- url     : https://prove2.me/theorems/fcfb144f-6479-4a72-a877-23fcc7254031
-- title:
--   Qubit: pauli Z pauli X trace
-- statement:
--   The Qubit construction uses the pauli Z pauli X trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L341-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L341-L344

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

theorem QEC.Semantics.Qubit.pauliZ_pauliX_trace :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliX) = 0 := by sorry
