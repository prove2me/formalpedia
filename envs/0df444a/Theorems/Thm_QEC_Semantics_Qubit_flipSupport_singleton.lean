-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_flipSupport_singleton
-- name    : QEC.Semantics.Qubit.flipSupport_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:39.923196+00:00
-- url     : https://prove2.me/theorems/42c04b69-9720-4fc4-b436-3aa6d15ee317
-- title:
--   Qubit: flip Support singleton
-- statement:
--   The Qubit construction uses the flip Support singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L520-L526
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L520-L526

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
omit [Fintype ι]

theorem QEC.Semantics.Qubit.flipSupport_singleton (i : ι) (bits : Bitstring ι) :
    flipSupport ({i} : Finset ι) bits = flipAt i bits := by sorry
