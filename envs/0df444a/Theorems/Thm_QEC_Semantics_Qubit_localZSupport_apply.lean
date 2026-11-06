-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
-- name    : QEC.Semantics.Qubit.localZSupport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:28.72019+00:00
-- url     : https://prove2.me/theorems/b300c43f-579e-4185-ab1f-8053b461efc2
-- title:
--   Qubit: local ZSupport apply
-- statement:
--   The Qubit construction uses the local ZSupport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L561-L564
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L561-L564

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

theorem QEC.Semantics.Qubit.localZSupport_apply (s : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localZSupport s ψ bits = zSupportPhase s bits * ψ bits := by sorry

attribute [defeq] QEC.Semantics.Qubit.localZSupport_apply
