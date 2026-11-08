-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_decodeTyped_output
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.decodeTyped_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:14:23.042203+00:00
-- url     : https://prove2.me/theorems/922ba01d-4504-4724-8d5c-420572e84c8a
-- title:
--   LPSSparse Emitter Family: decode Typed output
-- statement:
--   The LPSSparse Emitter Family construction uses the decode Typed output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L61-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L61-L67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_decodeTyped_output

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.decodeTyped_output {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeTyped
 (D*(D*(lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 B).q).length)+
 (2*r)*((2*r')*(lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 B).q).length)) s (output hp hp4 B g t h h')=
 some (lpsEncodedCheckOutput t (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) h h'):= by sorry
