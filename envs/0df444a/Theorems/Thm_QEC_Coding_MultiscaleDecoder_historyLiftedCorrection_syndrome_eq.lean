-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_historyLiftedCorrection_syndrome_eq
-- name    : QEC.Coding.MultiscaleDecoder.historyLiftedCorrection_syndrome_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:23.957103+00:00
-- url     : https://prove2.me/theorems/49456dd3-e06a-4cb2-8d76-8da82251e487
-- title:
--   Multiscale Decoder: history Lifted Correction syndrome eq
-- statement:
--   The Multiscale Decoder construction uses the history Lifted Correction syndrome eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1197-L1206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1197-L1206

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

theorem QEC.Coding.MultiscaleDecoder.historyLiftedCorrection_syndrome_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.coboundary1 (TopIndex depth)
        (historyLiftedCorrection D (buildCorrectionHistory D S B sigma)) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by sorry
