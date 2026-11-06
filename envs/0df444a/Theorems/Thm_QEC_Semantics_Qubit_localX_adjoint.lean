-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localX_adjoint
-- name    : QEC.Semantics.Qubit.localX_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:59.805138+00:00
-- url     : https://prove2.me/theorems/fb11d9cf-f051-4375-91c6-a0e2cf80fe08
-- title:
--   Qubit: local X adjoint
-- statement:
--   The Qubit construction uses the local X adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L458-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L458-L463

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

theorem QEC.Semantics.Qubit.localX_adjoint (i : ι) : LinearMap.adjoint (localX i) = localX i := by sorry
