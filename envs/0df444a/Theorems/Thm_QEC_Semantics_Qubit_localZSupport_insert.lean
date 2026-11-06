-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZSupport_insert
-- name    : QEC.Semantics.Qubit.localZSupport_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:51.792228+00:00
-- url     : https://prove2.me/theorems/61248e80-a820-41af-a97b-6cd510daabe6
-- title:
--   Qubit: local ZSupport insert
-- statement:
--   The Qubit construction uses the local ZSupport insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L581-L584
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L581-L584

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

theorem QEC.Semantics.Qubit.localZSupport_insert (s : Finset ι) {i : ι} (h : i ∉ s) :
    localZSupport (insert i s) = localZ i * localZSupport s := by sorry
