-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_pauliY_pauliX
-- name    : QEC.Semantics.Qubit.pauliY_pauliX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:15.900168+00:00
-- url     : https://prove2.me/theorems/7562de6b-b2fb-4986-88ed-965b09970d41
-- title:
--   Qubit: pauli Y pauli X
-- statement:
--   The Qubit construction uses the pauli Y pauli X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L255-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L255-L257

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

theorem QEC.Semantics.Qubit.pauliY_pauliX : pauliY * pauliX = -Complex.I • pauliZ := by sorry
