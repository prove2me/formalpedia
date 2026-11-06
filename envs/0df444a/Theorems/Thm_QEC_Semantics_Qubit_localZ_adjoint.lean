-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZ_adjoint
-- name    : QEC.Semantics.Qubit.localZ_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:04.231588+00:00
-- url     : https://prove2.me/theorems/3061ee75-259b-416b-8b54-d75577288edf
-- title:
--   Qubit: local Z adjoint
-- statement:
--   The Qubit construction uses the local Z adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L465-L470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L465-L470

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

theorem QEC.Semantics.Qubit.localZ_adjoint (i : ι) : LinearMap.adjoint (localZ i) = localZ i := by sorry
