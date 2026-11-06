-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_singleton
-- name    : QEC.Semantics.Qubit.localXSupport_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:58.998789+00:00
-- url     : https://prove2.me/theorems/ae96aedc-dec9-49ae-b6a9-87a7a60c7029
-- title:
--   Qubit: local XSupport singleton
-- statement:
--   The Qubit construction uses the local XSupport singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L566-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L566-L569

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

theorem QEC.Semantics.Qubit.localXSupport_singleton (i : ι) :
    localXSupport ({i} : Finset ι) = localX i := by sorry
