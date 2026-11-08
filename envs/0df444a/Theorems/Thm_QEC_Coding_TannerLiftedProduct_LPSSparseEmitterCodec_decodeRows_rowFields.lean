-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decodeRows_rowFields
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeRows_rowFields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:34:44.81411+00:00
-- url     : https://prove2.me/theorems/80654fd9-48dc-4560-b92e-0755b7e4e7e8
-- title:
--   LPSSparse Emitter Codec: decode Rows row Fields
-- statement:
--   The LPSSparse Emitter Codec construction uses the decode Rows row Fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L42-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L42-L50

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeRows_rowFields (rs:List Row) (tail:List ℕ):
 decodeRows rs.length (rowFields rs++tail)=some (rs,tail):= by sorry
