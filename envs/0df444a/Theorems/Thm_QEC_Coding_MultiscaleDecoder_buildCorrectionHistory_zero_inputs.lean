-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_zero_inputs
-- name    : QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_zero_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:23:56.30748+00:00
-- url     : https://prove2.me/theorems/332828ba-3120-4dc0-95ea-fcf400b50c92
-- title:
--   Multiscale Decoder: build Correction History zero inputs
-- statement:
--   Zero-preserving steps retain zero input snapshots throughout the fixed history.
--   No assertion is made about corrections or local pieces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L985-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L985-L1015

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

theorem QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_zero_inputs
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (hzero : ∀ i sigma, sigma.val = 0 → (S.step i sigma).coarse.val = 0)
    (sigma : D.family.Syndrome (TopIndex depth)) (hs : sigma.val = 0) :
    ∀ e ∈ buildCorrectionHistory D S B sigma, e.inputSyndrome.2.val = 0 := by sorry
