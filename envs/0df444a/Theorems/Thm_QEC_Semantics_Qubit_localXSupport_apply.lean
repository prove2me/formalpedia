-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
-- name    : QEC.Semantics.Qubit.localXSupport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:24.484963+00:00
-- url     : https://prove2.me/theorems/55bbd2a1-de3c-4a27-8740-0373f15224f6
-- title:
--   Qubit: local XSupport apply
-- statement:
--   The Qubit construction uses the local XSupport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L556-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L556-L559

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

theorem QEC.Semantics.Qubit.localXSupport_apply (s : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localXSupport s ψ bits = ψ (flipSupport s bits) := by sorry

attribute [defeq] QEC.Semantics.Qubit.localXSupport_apply
