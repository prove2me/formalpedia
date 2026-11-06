-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localX_localZ_commute_of_ne
-- name    : QEC.Semantics.Qubit.localX_localZ_commute_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:16.692944+00:00
-- url     : https://prove2.me/theorems/dd5d5ade-00fe-4c99-ac09-e8baef390f0c
-- title:
--   Qubit: local X local Z commute of ne
-- statement:
--   The Qubit construction uses the local X local Z commute of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L477-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L477-L481

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

theorem QEC.Semantics.Qubit.localX_localZ_commute_of_ne {i j : ι} (h : i ≠ j) :
    localX i * localZ j = localZ j * localX i := by sorry
