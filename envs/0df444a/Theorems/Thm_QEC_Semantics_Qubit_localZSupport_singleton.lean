-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZSupport_singleton
-- name    : QEC.Semantics.Qubit.localZSupport_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:37.068897+00:00
-- url     : https://prove2.me/theorems/99913677-c03a-4607-acd5-1124d52b778f
-- title:
--   Qubit: local ZSupport singleton
-- statement:
--   The Qubit construction uses the local ZSupport singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L571-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L571-L574

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

theorem QEC.Semantics.Qubit.localZSupport_singleton (i : ι) :
    localZSupport ({i} : Finset ι) = localZ i := by sorry
