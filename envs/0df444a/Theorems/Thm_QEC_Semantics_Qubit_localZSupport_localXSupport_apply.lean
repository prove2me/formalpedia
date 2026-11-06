-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZSupport_localXSupport_apply
-- name    : QEC.Semantics.Qubit.localZSupport_localXSupport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:33.521657+00:00
-- url     : https://prove2.me/theorems/111f4895-c4fd-4af2-b78c-ce8dcaf98c72
-- title:
--   Qubit: local ZSupport local XSupport apply
-- statement:
--   The Qubit construction uses the local ZSupport local XSupport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L606-L610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L606-L610

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

theorem QEC.Semantics.Qubit.localZSupport_localXSupport_apply (xSupport zSupport : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    (localZSupport zSupport * localXSupport xSupport) ψ bits =
      zSupportPhase zSupport bits * ψ (flipSupport xSupport bits) := by sorry
