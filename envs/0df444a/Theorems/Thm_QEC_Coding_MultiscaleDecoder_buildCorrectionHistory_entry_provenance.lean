-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_entry_provenance
-- name    : QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_entry_provenance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:25:36.410201+00:00
-- url     : https://prove2.me/theorems/63c78db1-103a-4c27-8283-0acd0be8dc5d
-- title:
--   Multiscale Decoder: build Correction History entry provenance
-- statement:
--   Every generated entry retains its actual decoder provenance. In particular,
--   the step output is computed from its own stored input and the base correction
--   is computed by the selected base decoder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L715-L747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L715-L747

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

theorem QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_entry_provenance
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex depth)) :
    ∀ e ∈ buildCorrectionHistory D S B sigma,
      match e with
      | .base b => b.correction = B.decode b.input
      | .step i out => out = S.step i out.input := by sorry
