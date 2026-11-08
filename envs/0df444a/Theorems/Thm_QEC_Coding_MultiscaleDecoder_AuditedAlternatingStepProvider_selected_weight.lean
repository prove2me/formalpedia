-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_AuditedAlternatingStepProvider_selected_weight
-- name    : QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider.selected_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:53.426311+00:00
-- url     : https://prove2.me/theorems/b5011404-3e51-4476-8d2e-dcd43a66286b
-- title:
--   Audited Alternating Step Provider: selected weight
-- statement:
--   The Audited Alternating Step Provider construction uses the selected weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L439-L457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L439-L457

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
open QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider
variable {D : BDL26DecoderData depth C0 C1 C2}

theorem QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider.selected_weight
    (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) (sigma : D.family.Syndrome i.succ) :
    (i.succ.val % 2 = 1 ∧
      2 * HammingWeight ((P.selected i sigma).coarse : D.family.Cochain2 i.castSucc) ≤
        HammingWeight (sigma : D.family.Cochain2 i.succ)) ∨
    (i.succ.val % 2 ≠ 1 ∧
      HammingWeight ((P.selected i sigma).coarse : D.family.Cochain2 i.castSucc) ≤
        HammingWeight (sigma : D.family.Cochain2 i.succ)) := by sorry
