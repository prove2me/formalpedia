-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_decodeTyped_output
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.decodeTyped_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:41:03.50183+00:00
-- url     : https://prove2.me/theorems/a8764914-ee66-4e3c-b550-68e067d3166a
-- title:
--   LPSSparse Emitter Source: decode Typed output
-- statement:
--   The LPSSparse Emitter Source construction uses the decode Typed output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L282-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L282-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.decodeTyped_output {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeTyped
 (D*(D*(lpsPSLList a.q).length)+(2*r)*((2*r')*(lpsPSLList a.q).length)) s (output a g t h h')=
 some (lpsEncodedCheckOutput t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h'):= by sorry
