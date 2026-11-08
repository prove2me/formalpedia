-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_xSpecs_length
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.xSpecs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:46:16.140199+00:00
-- url     : https://prove2.me/theorems/96d43acb-5f7c-4aec-83bf-bd02158cd275
-- title:
--   LPSSparse Emitter Source: x Specs length
-- statement:
--   The LPSSparse Emitter Source construction uses the x Specs length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L51-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L51-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open LPSSparseEmitterRow
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.xSpecs_length {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s))
 (h':Matrix (Fin r') (Fin D) (Fin s)) (ar:Fin (2*r)) (br:Fin D) (scalar:Fin s):
 (xSpecs t h h' ar br scalar).length=D+2*r':= by sorry
