-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_localXMatrix_conjTranspose
-- name    : QEC.Semantics.Qubit.localXMatrix_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:55.749644+00:00
-- url     : https://prove2.me/theorems/98ebefe7-4648-4d2f-bead-a379f4d0a824
-- title:
--   Qubit: local XMatrix conj Transpose
-- statement:
--   The Qubit construction uses the local XMatrix conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L417-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L417-L444

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

theorem QEC.Semantics.Qubit.localXMatrix_conjTranspose (i : ι) :
    (localXMatrix i).conjTranspose = localXMatrix i := by sorry
