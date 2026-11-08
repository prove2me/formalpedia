-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_zSpecs_length
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.zSpecs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:49:38.145319+00:00
-- url     : https://prove2.me/theorems/391a6dea-37e3-403c-a4d1-bb9d64bec767
-- title:
--   LPSSparse Emitter Source: z Specs length
-- statement:
--   The LPSSparse Emitter Source construction uses the z Specs length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L54-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L54-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open LPSSparseEmitterRow
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.zSpecs_length {D r r' s:ℕ} (t:EncodedFieldTables s) (h:Matrix (Fin r) (Fin D) (Fin s))
 (h':Matrix (Fin r') (Fin D) (Fin s)) (ac:Fin D) (bc:Fin (2*r')) (scalar:Fin s):
 (zSpecs t h h' ac bc scalar).length=D+2*r:= by sorry
