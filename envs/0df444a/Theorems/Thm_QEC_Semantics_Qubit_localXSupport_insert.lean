-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_insert
-- name    : QEC.Semantics.Qubit.localXSupport_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:31.000749+00:00
-- url     : https://prove2.me/theorems/db1f8bb0-847a-4de3-b182-376b171e7907
-- title:
--   Qubit: local XSupport insert
-- statement:
--   The Qubit construction uses the local XSupport insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L576-L579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L576-L579

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

theorem QEC.Semantics.Qubit.localXSupport_insert (s : Finset ι) {i : ι} (h : i ∉ s) :
    localXSupport (insert i s) = localX i * localXSupport s := by sorry
