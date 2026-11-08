-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_output_eq_original
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.output_eq_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:46:47.402335+00:00
-- url     : https://prove2.me/theorems/da9451ca-6631-4736-a756-5a4b253e98e7
-- title:
--   LPSSparse Emitter Family: output eq original
-- statement:
--   The LPSSparse Emitter Family construction uses the output eq original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L52-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L52-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.output_eq_original {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 output hp hp4 B g t h h'=LPSSparseEmitterCodec.encode
 ((lpsEncodedCheckOutput t (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) h h').map
 (fun rs=>rs.map (fun e=>(e.1.val,e.2.val)))):= by sorry
