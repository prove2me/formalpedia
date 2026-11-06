-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localZMatrix_conjTranspose
-- name    : QEC.Semantics.Qubit.localZMatrix_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:47.169861+00:00
-- url     : https://prove2.me/theorems/94c8e64a-6734-4ae0-865e-721642ed35c7
-- title:
--   Qubit: local ZMatrix conj Transpose
-- statement:
--   The Qubit construction uses the local ZMatrix conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L447-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L447-L456

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
omit [DecidableEq ι]

theorem QEC.Semantics.Qubit.localZMatrix_conjTranspose (i : ι) :
    (localZMatrix i).conjTranspose = localZMatrix i := by sorry
