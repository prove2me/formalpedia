-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_localZSupport_apply
-- name    : QEC.Semantics.Qubit.localXSupport_localZSupport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:41.434172+00:00
-- url     : https://prove2.me/theorems/45fb4bdf-2b16-4791-a1f9-42d6e3872c18
-- title:
--   Qubit: local XSupport local ZSupport apply
-- statement:
--   The Qubit construction uses the local XSupport local ZSupport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L599-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L599-L604

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

theorem QEC.Semantics.Qubit.localXSupport_localZSupport_apply (xSupport zSupport : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    (localXSupport xSupport * localZSupport zSupport) ψ bits =
      zSupportPhase zSupport (flipSupport xSupport bits) *
        ψ (flipSupport xSupport bits) := by sorry
