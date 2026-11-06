-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXSupport_localZSupport_phase
-- name    : QEC.Semantics.Qubit.localXSupport_localZSupport_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:51.440488+00:00
-- url     : https://prove2.me/theorems/be3b1574-577b-4331-872d-c99cbefb0e5b
-- title:
--   Qubit: local XSupport local ZSupport phase
-- statement:
--   The Qubit construction uses the local XSupport local ZSupport phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L612-L617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L612-L617

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

theorem QEC.Semantics.Qubit.localXSupport_localZSupport_phase (xSupport zSupport : Finset ι) :
    localXSupport xSupport * localZSupport zSupport =
      supportPhaseSign xSupport zSupport •
        (localZSupport zSupport * localXSupport xSupport) := by sorry
