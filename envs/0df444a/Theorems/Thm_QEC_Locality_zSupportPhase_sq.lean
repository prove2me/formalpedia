-- Prove2me | Theorems.Thm_QEC_Locality_zSupportPhase_sq
-- name    : QEC.Locality.zSupportPhase_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:20.1492+00:00
-- url     : https://prove2.me/theorems/e71d1236-61a0-4271-a667-c35eb4f2489e
-- title:
--   Locality: z Support Phase sq
-- statement:
--   The Locality construction uses the z Support Phase sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L296-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L296-L302

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.zSupportPhase_sq {α : Type u} [DecidableEq α]
    (s : Finset α) (bits : Qubit.Bitstring α) :
    Qubit.zSupportPhase s bits * Qubit.zSupportPhase s bits = 1 := by sorry
