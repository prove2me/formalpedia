-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZ_localX_commute_of_ne
-- name    : QEC.Semantics.Qubit.localZ_localX_commute_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:01.424034+00:00
-- url     : https://prove2.me/theorems/d209b83b-65e2-4e93-aac7-7d981828ce8f
-- title:
--   Qubit: local Z local X commute of ne
-- statement:
--   The Qubit construction uses the local Z local X commute of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L483-L485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L483-L485

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

theorem QEC.Semantics.Qubit.localZ_localX_commute_of_ne {i j : ι} (h : i ≠ j) :
    localZ i * localX j = localX j * localZ i := by sorry
