-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_flipAt_commute
-- name    : QEC.Semantics.Qubit.flipAt_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:44.544052+00:00
-- url     : https://prove2.me/theorems/63c9cda7-9cdb-4ac0-8a74-7df60bcf7972
-- title:
--   Qubit: flip At commute
-- statement:
--   The Qubit construction uses the flip At commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L118-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L118-L131

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

theorem QEC.Semantics.Qubit.flipAt_commute {ι : Type u} [DecidableEq ι]
    (i j : ι) (bits : Bitstring ι) :
    flipAt i (flipAt j bits) = flipAt j (flipAt i bits) := by sorry
