-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZ_localZ_commute
-- name    : QEC.Semantics.Qubit.localZ_localZ_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:26.683208+00:00
-- url     : https://prove2.me/theorems/e8cba3af-f722-44e4-81fb-ef6077bac94a
-- title:
--   Qubit: local Z local Z commute
-- statement:
--   The Qubit construction uses the local Z local Z commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L492-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L492-L495

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

theorem QEC.Semantics.Qubit.localZ_localZ_commute (i j : ι) :
    localZ i * localZ j = localZ j * localZ i := by sorry
