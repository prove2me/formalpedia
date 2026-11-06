-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localX_localX_commute
-- name    : QEC.Semantics.Qubit.localX_localX_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:14.599077+00:00
-- url     : https://prove2.me/theorems/64c0a779-c9d1-4a65-a2bb-8707cd4ae98a
-- title:
--   Qubit: local X local X commute
-- statement:
--   The Qubit construction uses the local X local X commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L487-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L487-L490

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
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Qubit.localX_localX_commute (i j : ι) :
    localX i * localX j = localX j * localX i := by sorry
