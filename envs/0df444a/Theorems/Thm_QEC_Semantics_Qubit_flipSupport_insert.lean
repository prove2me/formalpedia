-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_flipSupport_insert
-- name    : QEC.Semantics.Qubit.flipSupport_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:29.599734+00:00
-- url     : https://prove2.me/theorems/91620b51-86b1-437b-a998-27bcb5e6d145
-- title:
--   Qubit: flip Support insert
-- statement:
--   The Qubit construction uses the flip Support insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L508-L517
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L508-L517

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

theorem QEC.Semantics.Qubit.flipSupport_insert (s : Finset ι) {i : ι} (h : i ∉ s)
    (bits : Bitstring ι) :
    flipSupport (insert i s) bits = flipSupport s (flipAt i bits) := by sorry
