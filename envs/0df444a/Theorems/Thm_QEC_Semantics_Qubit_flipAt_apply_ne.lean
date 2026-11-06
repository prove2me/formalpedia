-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_flipAt_apply_ne
-- name    : QEC.Semantics.Qubit.flipAt_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:56.106196+00:00
-- url     : https://prove2.me/theorems/83b6f932-c3bc-4348-8878-94dcf62c33a3
-- title:
--   Qubit: flip At apply ne
-- statement:
--   The Qubit construction uses the flip At apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L107-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L107-L110

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

theorem QEC.Semantics.Qubit.flipAt_apply_ne {ι : Type u} [DecidableEq ι]
    {i j : ι} (bits : Bitstring ι) (h : j ≠ i) :
    flipAt i bits j = bits j := by sorry
