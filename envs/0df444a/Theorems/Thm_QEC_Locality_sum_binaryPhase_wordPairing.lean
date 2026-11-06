-- Prove2me | Theorems.Thm_QEC_Locality_sum_binaryPhase_wordPairing
-- name    : QEC.Locality.sum_binaryPhase_wordPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:17.978214+00:00
-- url     : https://prove2.me/theorems/3bfbc763-6f58-4200-9361-7fea3e7b803f
-- title:
--   Locality: sum binary Phase word Pairing
-- statement:
--   The Locality construction uses the sum binary Phase word Pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L319-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L319-L341

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

theorem QEC.Locality.sum_binaryPhase_wordPairing {α : Type u} [Fintype α] [DecidableEq α]
    (r : Coding.Word (ZMod 2) α) :
    ∑ z : Coding.Word (ZMod 2) α,
      PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := α) z r) =
      if r = 0 then Fintype.card (Coding.Word (ZMod 2) α) else 0 := by sorry
