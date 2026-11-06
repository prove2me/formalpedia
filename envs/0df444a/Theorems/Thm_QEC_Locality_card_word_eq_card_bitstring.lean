-- Prove2me | Theorems.Thm_QEC_Locality_card_word_eq_card_bitstring
-- name    : QEC.Locality.card_word_eq_card_bitstring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:27.06245+00:00
-- url     : https://prove2.me/theorems/344acbff-3742-41d9-b19e-c8088995022e
-- title:
--   Locality: card word eq card bitstring
-- statement:
--   The Locality construction uses the card word eq card bitstring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L403-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L403-L406

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

theorem QEC.Locality.card_word_eq_card_bitstring (S : FiniteSubsystem ι) :
    Fintype.card (Coding.Word (ZMod 2) S.SelectedCoordinates) =
      Fintype.card (Qubit.Bitstring S.SelectedCoordinates) := by sorry
