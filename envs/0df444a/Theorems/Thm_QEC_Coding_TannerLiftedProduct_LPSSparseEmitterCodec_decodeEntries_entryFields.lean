-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decodeEntries_entryFields
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeEntries_entryFields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:33:37.146924+00:00
-- url     : https://prove2.me/theorems/a35a27a2-5389-4bc6-92eb-7c900a60b23e
-- title:
--   LPSSparse Emitter Codec: decode Entries entry Fields
-- statement:
--   The LPSSparse Emitter Codec construction uses the decode Entries entry Fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L33-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L33-L41

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeEntries_entryFields (r:Row) (tail:List ℕ):
 decodeEntries r.length (entryFields r++tail)=some (r,tail):= by sorry
