-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_base_weight
-- name    : QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_base_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:20.114451+00:00
-- url     : https://prove2.me/theorems/0acdfc41-9799-4167-b30f-ac8d5f5d1e47
-- title:
--   Multiscale Decoder: build Correction History base weight
-- statement:
--   The accumulated bound is on the stored base snapshot itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L969-L981
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L969-L981

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

theorem QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_base_weight
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (hstep : ∀ (i : StepIndex depth) (s : D.family.Syndrome i.succ),
      if i.val % 2 = 0 then
        2 * HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val
      else HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    2 ^ ((depth + 1) / 2) *
      HammingWeight (historyInputReadout D (buildCorrectionHistory D S B sigma) 0) ≤
        HammingWeight sigma.val := by sorry
