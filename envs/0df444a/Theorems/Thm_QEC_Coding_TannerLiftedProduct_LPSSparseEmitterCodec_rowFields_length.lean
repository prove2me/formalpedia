-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_rowFields_length
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.rowFields_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:23:43.80624+00:00
-- url     : https://prove2.me/theorems/7abff865-dfe4-4b7e-89ef-1a78ef2f30ef
-- title:
--   LPSSparse Emitter Codec: row Fields length
-- statement:
--   The LPSSparse Emitter Codec construction uses the row Fields length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L68-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L68-L73

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.rowFields_length (rs:List Row):(rowFields rs).length=rs.length+2*(rs.map List.length).sum:= by sorry
