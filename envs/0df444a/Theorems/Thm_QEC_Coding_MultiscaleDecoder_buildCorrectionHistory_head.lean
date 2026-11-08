-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_head
-- name    : QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:23:49.112817+00:00
-- url     : https://prove2.me/theorems/969b27d8-1ac9-4500-8359-a6bc13e7afec
-- title:
--   Multiscale Decoder: build Correction History head
-- statement:
--   The actual nonempty history starts with the canonical top step. This
--   exposes only the head and leaves the recursively constructed tail intact.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L751-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L751-L761

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_head
    (n : Nat) {A0 A1 A2 : LevelIndex (n + 1) → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData (n + 1) A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex (n + 1))) :
    ∃ tail, buildCorrectionHistory D S B sigma =
      CorrectionHistoryEntry.step (Fin.last n) (S.step (Fin.last n) sigma) :: tail := by sorry
